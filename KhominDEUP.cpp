#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <lzma.h>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace fs = std::filesystem;

using Byte = std::uint8_t;
using Bytes = std::vector<Byte>;

[[noreturn]] static void fail(const std::string &message) {
    throw std::runtime_error(message);
}

static std::uint16_t read16(const Bytes &data, std::size_t off) {
    if (off + 2 > data.size()) fail("unexpected end of file");
    return static_cast<std::uint16_t>(data[off]) |
           (static_cast<std::uint16_t>(data[off + 1]) << 8);
}

static std::uint32_t read32(const Bytes &data, std::size_t off) {
    if (off + 4 > data.size()) fail("unexpected end of file");
    return static_cast<std::uint32_t>(data[off]) |
           (static_cast<std::uint32_t>(data[off + 1]) << 8) |
           (static_cast<std::uint32_t>(data[off + 2]) << 16) |
           (static_cast<std::uint32_t>(data[off + 3]) << 24);
}

static std::uint64_t read64(const Bytes &data, std::size_t off) {
    if (off + 8 > data.size()) fail("unexpected end of buffer");
    std::uint64_t value = 0;
    for (unsigned i = 0; i < 8; ++i)
        value |= static_cast<std::uint64_t>(data[off + i]) << (i * 8);
    return value;
}

static std::uint64_t readBe64(const Bytes &data, std::size_t off) {
    if (off + 8 > data.size()) fail("unexpected end of buffer");
    std::uint64_t value = 0;
    for (unsigned i = 0; i < 8; ++i)
        value = (value << 8) | data[off + i];
    return value;
}

static void write16(Bytes &data, std::size_t off, std::uint16_t value) {
    if (off + 2 > data.size()) fail("write outside buffer");
    data[off] = static_cast<Byte>(value);
    data[off + 1] = static_cast<Byte>(value >> 8);
}

static void write32(Bytes &data, std::size_t off, std::uint32_t value) {
    if (off + 4 > data.size()) fail("write outside buffer");
    data[off] = static_cast<Byte>(value);
    data[off + 1] = static_cast<Byte>(value >> 8);
    data[off + 2] = static_cast<Byte>(value >> 16);
    data[off + 3] = static_cast<Byte>(value >> 24);
}

static void write64(Bytes &data, std::size_t off, std::uint64_t value) {
    if (off + 8 > data.size()) fail("write outside buffer");
    for (unsigned i = 0; i < 8; ++i)
        data[off + i] = static_cast<Byte>(value >> (i * 8));
}

static std::size_t alignUp(std::size_t value, std::size_t alignment) {
    if (alignment == 0) fail("zero alignment");
    const std::size_t remainder = value % alignment;
    return remainder == 0 ? value : value + alignment - remainder;
}

static Bytes readFile(const fs::path &path) {
    std::ifstream in(path, std::ios::binary | std::ios::ate);
    if (!in) fail("cannot open input: " + path.string());
    const auto end = in.tellg();
    if (end < 0) fail("cannot determine input size");
    Bytes data(static_cast<std::size_t>(end));
    in.seekg(0);
    if (!data.empty() && !in.read(reinterpret_cast<char *>(data.data()), end))
        fail("cannot read input");
    return data;
}

static void writeFile(const fs::path &path, const Bytes &data) {
    std::ofstream out(path, std::ios::binary | std::ios::trunc);
    if (!out) fail("cannot create output: " + path.string());
    if (!data.empty())
        out.write(reinterpret_cast<const char *>(data.data()),
                  static_cast<std::streamsize>(data.size()));
    if (!out) fail("cannot write output");
}

struct Section {
    std::array<char, 8> name{};
    std::uint32_t virtualSize{};
    std::uint32_t virtualAddress{};
    std::uint32_t rawSize{};
    std::uint32_t rawOffset{};
    std::uint32_t characteristics{};
    std::size_t headerOffset{};
};

struct PeImage {
    std::size_t peOffset{};
    std::size_t optionalOffset{};
    std::size_t sectionTableOffset{};
    std::uint16_t machine{};
    std::uint16_t optionalMagic{};
    std::uint16_t optionalSize{};
    std::uint32_t entryRva{};
    std::uint32_t sizeOfHeaders{};
    std::vector<Section> sections;
};

static PeImage parsePe(const Bytes &data) {
    if (data.size() < 0x40 || data[0] != 'M' || data[1] != 'Z')
        fail("not an MZ executable");

    PeImage pe;
    pe.peOffset = read32(data, 0x3c);
    if (pe.peOffset + 24 > data.size() ||
        std::memcmp(data.data() + pe.peOffset, "PE\0\0", 4) != 0)
        fail("invalid PE signature");

    pe.machine = read16(data, pe.peOffset + 4);
    const auto sectionCount = read16(data, pe.peOffset + 6);
    pe.optionalSize = read16(data, pe.peOffset + 20);
    pe.optionalOffset = pe.peOffset + 24;
    if (pe.optionalOffset + pe.optionalSize > data.size())
        fail("truncated optional header");
    pe.optionalMagic = read16(data, pe.optionalOffset);
    if (pe.optionalMagic != 0x10b && pe.optionalMagic != 0x20b)
        fail("unsupported PE optional header");
    pe.entryRva = read32(data, pe.optionalOffset + 16);
    pe.sizeOfHeaders = read32(data, pe.optionalOffset + 60);
    pe.sectionTableOffset = pe.optionalOffset + pe.optionalSize;

    if (pe.sectionTableOffset + static_cast<std::size_t>(sectionCount) * 40 > data.size())
        fail("truncated section table");
    pe.sections.reserve(sectionCount);
    for (std::uint16_t i = 0; i < sectionCount; ++i) {
        const std::size_t off = pe.sectionTableOffset + static_cast<std::size_t>(i) * 40;
        Section s;
        std::memcpy(s.name.data(), data.data() + off, 8);
        s.virtualSize = read32(data, off + 8);
        s.virtualAddress = read32(data, off + 12);
        s.rawSize = read32(data, off + 16);
        s.rawOffset = read32(data, off + 20);
        s.characteristics = read32(data, off + 36);
        s.headerOffset = off;
        pe.sections.push_back(s);
    }
    return pe;
}

static std::size_t rvaToFileOffset(const PeImage &pe, std::uint32_t rva) {
    if (rva < pe.sizeOfHeaders) return rva;
    for (const auto &s : pe.sections) {
        const std::uint32_t span = std::max(s.virtualSize, s.rawSize);
        if (rva >= s.virtualAddress && rva - s.virtualAddress < span)
            return static_cast<std::size_t>(s.rawOffset) + (rva - s.virtualAddress);
    }
    fail("RVA is not backed by file data");
}

struct PackHeader {
    std::size_t offset{};
    std::uint8_t version{};
    std::uint8_t format{};
    std::uint8_t method{};
    std::uint8_t level{};
    std::uint32_t unpackedAdler{};
    std::uint32_t packedAdler{};
    std::uint32_t unpackedSize{};
    std::uint32_t packedSize{};
    std::uint32_t originalFileSize{};
    std::uint8_t filter{};
    std::uint8_t filterCto{};
    std::uint8_t filterMisc{};
    std::uint8_t checksum{};
};

struct StubFacts {
    std::uint32_t filteredCodeSize{};
    std::uint8_t filterCto{};
    bool hasFilter{};
};

static std::size_t findByteArray(const Bytes &data,
                                 std::size_t begin,
                                 std::size_t end,
                                 const Byte *pattern,
                                 std::size_t patternSize) {
    end = std::min(end, data.size());
    if (begin > end || patternSize > end - begin) return std::string::npos;
    const auto it = std::search(data.begin() + begin, data.begin() + end,
                                pattern, pattern + patternSize);
    return it == data.begin() + end ? std::string::npos
                                    : static_cast<std::size_t>(it - data.begin());
}

static StubFacts inspectStubBytes(const Bytes &file,
                                  const PeImage &pe,
                                  std::uint8_t method,
                                  std::uint8_t filterId) {
    static constexpr Byte nrv2bLoop[] = {
        0x8d, 0x41, 0x01, 0x41, 0xff, 0xd3, 0x11, 0xc0,
        0x01, 0xdb, 0x75, 0x0a, 0x8b, 0x1e, 0x48, 0x83,
        0xee, 0xfc, 0x11, 0xdb, 0x8a, 0x16, 0x73, 0xeb};
    static constexpr Byte nrv2dLoop[] = {
        0xd1, 0xf8, 0x48, 0x63, 0xe8, 0xeb, 0x03, 0x41, 0xff,
        0xd3, 0x11, 0xc9, 0x41, 0xff, 0xd3, 0x11, 0xc9, 0x75, 0x18};
    static constexpr Byte nrv2eLoop[] = {
        0xd1, 0xf8, 0x48, 0x63, 0xe8, 0x72, 0x38, 0xeb,
        0x0e, 0x01, 0xdb, 0x75, 0x08};
    static constexpr Byte lzmaSetup[] = {
        0x8a, 0x07, 0xff, 0xca, 0x88, 0xc1, 0x24, 0x07, 0xc0, 0xe9,
        0x03, 0x48, 0xc7, 0xc3, 0x00, 0xfd, 0xff, 0xff, 0x48, 0xd3, 0xe3};
    static constexpr Byte relocLoop[] = {
        0x31, 0xc0, 0x8a, 0x07, 0x48, 0xff, 0xc7, 0x09,
        0xc0, 0x74, 0x23, 0x3c, 0xef};
    static constexpr Byte filterPrefix[] = {0x48, 0xc7, 0xc6};

    const std::size_t entry = rvaToFileOffset(pe, pe.entryRva);
    const std::size_t end = std::min(file.size(), entry + 0x1200);
    if (method == 2) {
        if (findByteArray(file, entry, end, nrv2bLoop, sizeof(nrv2bLoop)) ==
            std::string::npos)
            fail("the NRV2B routine byte array was not found in the entry stub");
    } else if (method == 5) {
        if (findByteArray(file, entry, end, nrv2dLoop, sizeof(nrv2dLoop)) ==
            std::string::npos)
            fail("the NRV2D routine byte array was not found in the entry stub");
    } else if (method == 8) {
        if (findByteArray(file, entry, end, nrv2eLoop, sizeof(nrv2eLoop)) ==
            std::string::npos)
            fail("the NRV2E routine byte array was not found in the entry stub");
    } else if (method == 14) {
        if (findByteArray(file, entry, end, lzmaSetup, sizeof(lzmaSetup)) ==
            std::string::npos)
            fail("the LZMA routine byte array was not found in the entry stub");
    } else {
        fail("unsupported compression method " + std::to_string(method));
    }
    if (findByteArray(file, entry, end, relocLoop, sizeof(relocLoop)) == std::string::npos)
        fail("the DIR64 relocation routine byte array was not found in the entry stub");

    if (filterId == 0) return {};
    if (filterId != 0x49)
        fail("unsupported stub filter " + std::to_string(filterId));

    std::size_t filter = findByteArray(file, entry, end, filterPrefix, sizeof(filterPrefix));
    while (filter != std::string::npos) {
        if (filter + 9 <= file.size() && file[filter + 7] == 0xb2)
            return {read32(file, filter + 3), file[filter + 8], true};
        filter = findByteArray(file, filter + 1, end, filterPrefix, sizeof(filterPrefix));
    }
    fail("the x86-64 filter byte array was not found in the entry stub");
}

static std::vector<std::uint8_t> recoverHeaderVersions(const Bytes &data, std::size_t off) {
    unsigned known = 0;
    for (std::size_t i = 5; i <= 30; ++i) known += data[off + i];
    std::vector<std::uint8_t> versions;
    for (unsigned v = 1; v < 255; ++v) {
        if ((known + v) % 251 == data[off + 31])
            versions.push_back(static_cast<std::uint8_t>(v));
    }
    return versions;
}

static PackHeader findPackHeader(const Bytes &data, const PeImage &pe) {
    if (pe.sections.size() < 2) fail("too few sections for a packed PE");
    const std::uint8_t expectedFormat = pe.optionalMagic == 0x20b ? 36 : 9;
    const std::size_t entryRaw = rvaToFileOffset(pe, pe.entryRva);
    const std::size_t scanBegin = pe.sections[1].rawOffset > 64
                                      ? pe.sections[1].rawOffset - 64
                                      : 0;
    const std::size_t scanEnd = std::min(data.size() - 32, scanBegin + 1024);

    bool found = false;
    PackHeader best{};
    std::size_t bestGap = std::numeric_limits<std::size_t>::max();

    for (std::size_t off = scanBegin; off <= scanEnd; ++off) {
        if (data[off + 5] != expectedFormat) continue;
        const std::uint8_t method = data[off + 6];
        const std::uint8_t level = data[off + 7] & 0x0f;
        if (method < 2 || method > 14 || level == 0 || level > 10) continue;

        const auto versions = recoverHeaderVersions(data, off);
        auto it = std::find_if(versions.begin(), versions.end(), [](std::uint8_t v) {
            return v >= 10 && v < 64;
        });
        if (it == versions.end()) continue;

        const std::uint32_t unpackedSize = read32(data, off + 16);
        const std::uint32_t packedSize = read32(data, off + 20);
        const std::uint32_t originalFileSize = read32(data, off + 24);
        if (packedSize < 2 || unpackedSize < 2 || packedSize > unpackedSize) continue;
        if (originalFileSize < pe.sizeOfHeaders || originalFileSize > (1u << 30)) continue;

        const std::size_t packedBegin = off + 32;
        if (packedBegin + packedSize > data.size()) continue;
        if (packedBegin + packedSize > entryRaw) continue;
        const std::size_t gap = entryRaw - (packedBegin + packedSize);
        if (gap > 4096 || gap >= bestGap) continue;

        best = {off,
                *it,
                data[off + 5],
                method,
                level,
                read32(data, off + 8),
                read32(data, off + 12),
                unpackedSize,
                packedSize,
                originalFileSize,
                data[off + 28],
                data[off + 29],
                data[off + 30],
                data[off + 31]};
        bestGap = gap;
        found = true;
    }

    if (!found) fail("could not recover the damaged UPX header");
    return best;
}

class StubBitReader {
public:
    StubBitReader(const Byte *data, std::size_t size) : data_(data), size_(size) {}

    unsigned bit() {
        if (bitsLeft_ == 0) {
            if (pos_ + 4 > size_) fail("compressed stream ended inside bit word");
            word_ = static_cast<std::uint32_t>(data_[pos_]) |
                    (static_cast<std::uint32_t>(data_[pos_ + 1]) << 8) |
                    (static_cast<std::uint32_t>(data_[pos_ + 2]) << 16) |
                    (static_cast<std::uint32_t>(data_[pos_ + 3]) << 24);
            pos_ += 4;
            bitsLeft_ = 32;
        }
        const unsigned result = word_ >> 31;
        word_ <<= 1;
        --bitsLeft_;
        return result;
    }

    Byte byte() {
        if (pos_ >= size_) fail("compressed stream ended inside literal/match");
        return data_[pos_++];
    }

    std::size_t consumed() const { return pos_; }

private:
    const Byte *data_{};
    std::size_t size_{};
    std::size_t pos_{};
    std::uint32_t word_{};
    unsigned bitsLeft_{};
};

static Bytes decompressNrv2bLe32FromStub(const Byte *packed,
                                        std::size_t packedSize,
                                        std::size_t expectedSize) {
    StubBitReader in(packed, packedSize);
    Bytes out;
    out.reserve(expectedSize);
    std::size_t lastOffset = 1;

    for (;;) {
        while (in.bit() != 0) {
            if (out.size() >= expectedSize) fail("literal exceeds output buffer");
            out.push_back(in.byte());
        }

        std::uint32_t offsetCode = 1;
        do {
            offsetCode = offsetCode * 2u + in.bit();
            if (offsetCode > 0x01000002u) fail("invalid match offset code");
        } while (in.bit() == 0);

        std::size_t distance;
        if (offsetCode == 2) {
            distance = lastOffset;
        } else {
            std::uint32_t raw = (offsetCode - 3u) * 256u + in.byte();
            if (raw == 0xffffffffu) break;
            distance = static_cast<std::size_t>(raw) + 1;
            lastOffset = distance;
        }

        std::size_t length = in.bit();
        length = length * 2 + in.bit();
        if (length == 0) {
            length = 1;
            do {
                length = length * 2 + in.bit();
                if (length >= expectedSize) fail("invalid long match length");
            } while (in.bit() == 0);
            length += 2;
        }
        length += distance > 0x0d00 ? 1 : 0;
        ++length;

        if (distance == 0 || distance > out.size()) fail("invalid look-behind distance");
        if (length > expectedSize - out.size()) fail("match exceeds output buffer");
        for (std::size_t i = 0; i < length; ++i)
            out.push_back(out[out.size() - distance]);
    }

    if (out.size() != expectedSize)
        fail("decompressed size mismatch: got " + std::to_string(out.size()) +
             ", expected " + std::to_string(expectedSize));
    if (in.consumed() > packedSize)
        fail("compressed input overrun");
    return out;
}

static Bytes decompressNrv2dLe32FromStub(const Byte *packed,
                                         std::size_t packedSize,
                                         std::size_t expectedSize) {
    StubBitReader in(packed, packedSize);
    Bytes out;
    out.reserve(expectedSize);
    std::size_t lastOffset = 1;

    const auto appendOffsetBit = [&in](std::uint32_t &value) {
        const std::uint64_t next = static_cast<std::uint64_t>(value) * 2u + in.bit();
        if (next > 0x01000002u) fail("invalid NRV2D match offset code");
        value = static_cast<std::uint32_t>(next);
    };

    for (;;) {
        while (in.bit() != 0) {
            if (out.size() >= expectedSize) fail("literal exceeds output buffer");
            out.push_back(in.byte());
        }

        std::uint32_t offsetCode = 1;
        for (;;) {
            appendOffsetBit(offsetCode);
            if (in.bit() != 0) break;
            if (offsetCode == 0) fail("invalid NRV2D match offset code");
            --offsetCode;
            appendOffsetBit(offsetCode);
        }

        std::size_t distance;
        std::size_t length;
        if (offsetCode < 3) {
            distance = lastOffset;
            length = in.bit();
        } else {
            const std::uint32_t raw = (offsetCode - 3u) * 256u + in.byte();
            if (raw == 0xffffffffu) break;

            distance = static_cast<std::size_t>(raw >> 1) + 1;
            lastOffset = distance;
            length = (raw & 1u) == 0 ? 1u : 0u;
        }

        length = length * 2 + in.bit();
        if (length == 0) {
            length = 1;
            do {
                if (length > expectedSize / 2)
                    fail("invalid NRV2D long match length");
                length = length * 2 + in.bit();
            } while (in.bit() == 0);
            length += 2;
        }
        length += 1 + (distance > 0x500 ? 1 : 0);

        if (distance == 0 || distance > out.size()) fail("invalid look-behind distance");
        if (length > expectedSize - out.size()) fail("match exceeds output buffer");
        for (std::size_t i = 0; i < length; ++i)
            out.push_back(out[out.size() - distance]);
    }

    if (out.size() != expectedSize)
        fail("decompressed size mismatch: got " + std::to_string(out.size()) +
             ", expected " + std::to_string(expectedSize));
    if (in.consumed() > packedSize)
        fail("compressed input overrun");
    return out;
}

static Bytes decompressNrv2eLe32FromStub(const Byte *packed,
                                         std::size_t packedSize,
                                         std::size_t expectedSize) {
    StubBitReader in(packed, packedSize);
    Bytes out;
    out.reserve(expectedSize);
    std::size_t lastOffset = 1;

    const auto appendOffsetBit = [&in](std::uint32_t &value) {
        const std::uint64_t next = static_cast<std::uint64_t>(value) * 2u + in.bit();
        if (next > 0x01000002u) fail("invalid NRV2E match offset code");
        value = static_cast<std::uint32_t>(next);
    };

    for (;;) {
        while (in.bit() != 0) {
            if (out.size() >= expectedSize) fail("literal exceeds output buffer");
            out.push_back(in.byte());
        }

        std::uint32_t offsetCode = 1;
        for (;;) {
            appendOffsetBit(offsetCode);
            if (in.bit() != 0) break;
            if (offsetCode == 0) fail("invalid NRV2E match offset code");
            --offsetCode;
            appendOffsetBit(offsetCode);
        }

        std::size_t distance;
        std::size_t length = 0;
        bool decodeLastLengthBit;
        if (offsetCode < 3) {
            distance = lastOffset;
            decodeLastLengthBit = in.bit() != 0;
        } else {
            const std::uint32_t high = offsetCode - 3u;
            const std::uint32_t raw = high * 256u + in.byte();
            if (raw == 0xffffffffu) break;

            distance = static_cast<std::size_t>(raw >> 1) + 1;
            lastOffset = distance;
            decodeLastLengthBit = (raw & 1u) == 0;
        }

        if (!decodeLastLengthBit) {
            ++length;
            decodeLastLengthBit = in.bit() != 0;
            if (!decodeLastLengthBit) {
                do {
                    if (length > expectedSize / 2)
                        fail("invalid NRV2E long match length");
                    length = length * 2 + in.bit();
                } while (in.bit() == 0);
                length += 2;
            }
        }
        if (decodeLastLengthBit)
            length = length * 2 + in.bit();

        length += 2 + (distance > 0x500 ? 1 : 0);
        if (distance == 0 || distance > out.size()) fail("invalid look-behind distance");
        if (length > expectedSize - out.size()) fail("match exceeds output buffer");
        for (std::size_t i = 0; i < length; ++i)
            out.push_back(out[out.size() - distance]);
    }

    if (out.size() != expectedSize)
        fail("decompressed size mismatch: got " + std::to_string(out.size()) +
             ", expected " + std::to_string(expectedSize));
    if (in.consumed() > packedSize)
        fail("compressed input overrun");
    return out;
}

static Bytes decompressLzmaFromStub(const Byte *packed,
                                    std::size_t packedSize,
                                    std::size_t expectedSize) {
    if (packedSize < 7) fail("truncated LZMA stream");

    const unsigned packedProperties = packed[0];
    const unsigned pb = packedProperties & 7u;
    const unsigned lcPlusLp = packedProperties >> 3;
    const unsigned lp = packed[1] >> 4;
    const unsigned lc = packed[1] & 0x0fu;
    if (pb > 4 || lp > 4 || lc > 8 || lc + lp != lcPlusLp || lc + lp > 4)
        fail("invalid compact LZMA properties in entry stub stream");

    lzma_options_lzma options{};
    if (lzma_lzma_preset(&options, LZMA_PRESET_DEFAULT))
        fail("could not initialize the built-in LZMA decoder");
    options.lc = lc;
    options.lp = lp;
    options.pb = pb;
    options.dict_size = static_cast<std::uint32_t>(
        std::max<std::size_t>(4096, expectedSize));

    lzma_filter filters[] = {
        {LZMA_FILTER_LZMA1, &options},
        {LZMA_VLI_UNKNOWN, nullptr},
    };
    Bytes out(expectedSize);
    lzma_stream stream = LZMA_STREAM_INIT;
    lzma_ret result = lzma_raw_decoder(&stream, filters);
    if (result != LZMA_OK)
        fail("could not initialize raw LZMA decoding, status " +
             std::to_string(result));

    stream.next_in = packed + 2;
    stream.avail_in = packedSize - 2;
    stream.next_out = out.data();
    stream.avail_out = out.size();
    while (stream.avail_out != 0) {
        const std::size_t oldInput = stream.avail_in;
        const std::size_t oldOutput = stream.avail_out;
        result = lzma_code(&stream, LZMA_RUN);
        if (result != LZMA_OK && result != LZMA_STREAM_END) break;
        if (stream.avail_in == oldInput && stream.avail_out == oldOutput) {
            result = LZMA_BUF_ERROR;
            break;
        }
        if (result == LZMA_STREAM_END) break;
    }
    const std::size_t outputPosition = out.size() - stream.avail_out;
    lzma_end(&stream);

    if (result != LZMA_OK && result != LZMA_STREAM_END)
        fail("LZMA decoder failed with status " + std::to_string(result));
    if (outputPosition != expectedSize)
        fail("decompressed size mismatch: got " + std::to_string(outputPosition) +
             ", expected " + std::to_string(expectedSize));
    return out;
}

static std::uint32_t byteSwap32(std::uint32_t x) {
    return ((x & 0x000000ffu) << 24) |
           ((x & 0x0000ff00u) << 8) |
           ((x & 0x00ff0000u) >> 8) |
           ((x & 0xff000000u) >> 24);
}

static void unfilter49FromStub(Bytes &image,
                               std::size_t codeOffset,
                               std::size_t codeSize,
                               std::uint8_t cto) {
    if (codeOffset > image.size() || codeSize > image.size() - codeOffset)
        fail("filter range outside decompressed image");
    const std::size_t end = codeOffset + codeSize;
    std::size_t cursor = codeOffset;
    while (cursor + 5 <= end) {
        const std::size_t opcodeOffset = cursor;
        const Byte opcode = image[cursor++];
        const bool callOrJump = opcode == 0xe8 || opcode == 0xe9;
        const bool conditional = opcode >= 0x80 && opcode <= 0x8f &&
                                 opcodeOffset > codeOffset &&
                                 image[opcodeOffset - 1] == 0x0f;
        if (!callOrJump && !conditional) continue;
        if (cursor + 4 > end) break;

        const std::size_t operandOffset = cursor;
        std::uint32_t encoded = read32(image, operandOffset);
        cursor += 4;
        if (static_cast<Byte>(encoded) != cto) {
            cursor = operandOffset;
            continue;
        }

        const std::uint32_t absolute = byteSwap32(encoded);
        const std::uint32_t relative = absolute -
            (static_cast<std::uint32_t>(cto) << 24) -
            static_cast<std::uint32_t>(operandOffset - codeOffset);
        write32(image, operandOffset, relative);
    }
}

static std::uint32_t adler32(const Bytes &data) {
    constexpr std::uint32_t mod = 65521;
    std::uint32_t a = 1;
    std::uint32_t b = 0;
    for (Byte value : data) {
        a += value;
        if (a >= mod) a -= mod;
        b += a;
        b %= mod;
    }
    return (b << 16) | a;
}

static std::string hex32(std::uint32_t value) {
    std::ostringstream out;
    out << "0x" << std::hex << std::uppercase << std::setw(8)
        << std::setfill('0') << value;
    return out.str();
}

struct EmbeddedPe {
    std::size_t offset{};
    std::size_t headerSize{};
    std::size_t sectionTableOffset{};
    std::size_t metadataOffset{};
    std::size_t dataDirectoryOffset{};
    std::uint16_t optionalMagic{};
    std::uint16_t optionalSize{};
    std::uint32_t codeSize{};
    std::uint32_t codeBase{};
    std::uint32_t fileAlignment{};
    std::uint32_t sizeOfHeaders{};
    std::uint64_t imageBase{};
    std::vector<Section> sections;
};

static EmbeddedPe parseEmbeddedPe(const Bytes &image) {
    if (image.size() < 4) fail("decompressed image is too small");
    EmbeddedPe pe;
    pe.offset = read32(image, image.size() - 4);
    if (pe.offset + 24 > image.size() ||
        std::memcmp(image.data() + pe.offset, "PE\0\0", 4) != 0)
        fail("embedded PE metadata was not found");

    const std::uint16_t sectionCount = read16(image, pe.offset + 6);
    pe.optionalSize = read16(image, pe.offset + 20);
    const std::size_t optional = pe.offset + 24;
    if (optional + pe.optionalSize > image.size()) fail("truncated embedded optional header");
    pe.optionalMagic = read16(image, optional);
    if (pe.optionalMagic != 0x20b)
        fail("the recovered stub is PE32+ only; PE32 is not implemented yet");

    pe.headerSize = 24 + pe.optionalSize;
    pe.sectionTableOffset = pe.offset + pe.headerSize;
    pe.metadataOffset = pe.sectionTableOffset + static_cast<std::size_t>(sectionCount) * 40;
    if (pe.metadataOffset > image.size()) fail("truncated embedded section table");

    pe.codeSize = read32(image, optional + 4);
    pe.codeBase = read32(image, optional + 20);
    pe.imageBase = read64(image, optional + 24);
    pe.fileAlignment = read32(image, optional + 36);
    pe.sizeOfHeaders = read32(image, optional + 60);
    pe.dataDirectoryOffset = optional + 112;
    const std::uint32_t directoryCount = read32(image, optional + 108);
    if (directoryCount < 16 || pe.dataDirectoryOffset + 16 * 8 > image.size())
        fail("unexpected embedded data-directory table");

    pe.sections.reserve(sectionCount);
    for (std::uint16_t i = 0; i < sectionCount; ++i) {
        const std::size_t off = pe.sectionTableOffset + static_cast<std::size_t>(i) * 40;
        Section s;
        std::memcpy(s.name.data(), image.data() + off, 8);
        s.virtualSize = read32(image, off + 8);
        s.virtualAddress = read32(image, off + 12);
        s.rawSize = read32(image, off + 16);
        s.rawOffset = read32(image, off + 20);
        s.characteristics = read32(image, off + 36);
        s.headerOffset = off;
        pe.sections.push_back(s);
    }
    if (pe.sections.empty()) fail("embedded PE has no sections");
    return pe;
}

static std::uint32_t embeddedDirectoryRva(const Bytes &image,
                                          const EmbeddedPe &pe,
                                          unsigned index) {
    if (index >= 16) fail("bad data-directory index");
    return read32(image, pe.dataDirectoryOffset + static_cast<std::size_t>(index) * 8);
}

static std::uint32_t packedDirectoryRva(const Bytes &file,
                                        const PeImage &pe,
                                        unsigned index) {
    const std::size_t dd = pe.optionalOffset + (pe.optionalMagic == 0x20b ? 112 : 96);
    if (dd + static_cast<std::size_t>(index + 1) * 8 >
        pe.optionalOffset + pe.optionalSize)
        return 0;
    return read32(file, dd + static_cast<std::size_t>(index) * 8);
}

static std::size_t imageOffset(std::uint32_t rva,
                               std::uint32_t firstRva,
                               std::size_t size,
                               const char *what) {
    if (rva < firstRva) fail(std::string(what) + " RVA precedes the decompressed image");
    const std::size_t off = static_cast<std::size_t>(rva - firstRva);
    if (off > size) fail(std::string(what) + " RVA lies outside the decompressed image");
    return off;
}

static std::string readAsciiZ(const Bytes &data, std::size_t off, std::size_t limit) {
    if (off >= data.size() || off >= limit) fail("string offset outside buffer");
    std::string result;
    while (off < data.size() && off < limit && data[off] != 0)
        result.push_back(static_cast<char>(data[off++]));
    if (off >= data.size() || off >= limit) fail("unterminated string");
    return result;
}

static void copyAsciiZ(Bytes &destination, std::size_t off, const std::string &text) {
    if (off + text.size() + 1 > destination.size()) fail("string destination outside image");
    std::memcpy(destination.data() + off, text.data(), text.size());
    destination[off + text.size()] = 0;
}

static void rebuildImportsFromStub(Bytes &image,
                                   const EmbeddedPe &outPe,
                                   const Bytes &packedFile,
                                   const PeImage &packedPe,
                                   std::uint32_t metadataRva) {
    const std::uint32_t firstRva = outPe.sections.front().virtualAddress;
    const std::uint32_t importRva = embeddedDirectoryRva(image, outPe, 1);
    const std::uint32_t packedImportRva = packedDirectoryRva(packedFile, packedPe, 1);
    if (importRva == 0) return;
    if (packedImportRva == 0) fail("packed import helper table is missing");

    std::size_t meta = imageOffset(metadataRva, firstRva, image.size(), "import metadata");
    std::size_t descriptor = imageOffset(importRva, firstRva, image.size(), "import table");
    const std::size_t packedImport = rvaToFileOffset(packedPe, packedImportRva);

    for (unsigned dllCount = 0; dllCount < 1024; ++dllCount) {
        const std::uint32_t dllNameDelta = read32(image, meta);
        if (dllNameDelta == 0) return;
        const std::uint32_t iatDelta = read32(image, meta + 4);
        meta += 8;

        if (descriptor + 20 > image.size()) fail("import descriptor outside image");
        const std::uint32_t dllNameRva = read32(image, descriptor + 12);
        const std::size_t dllSource = packedImport + dllNameDelta;
        const std::string dllName = readAsciiZ(packedFile, dllSource, packedFile.size());
        copyAsciiZ(image, imageOffset(dllNameRva, firstRva, image.size(), "DLL name"), dllName);

        const std::uint32_t iatRva = firstRva + iatDelta;
        write32(image, descriptor + 16, iatRva);
        std::size_t thunk = imageOffset(iatRva, firstRva, image.size(), "IAT");

        for (unsigned functionCount = 0; functionCount < 65536; ++functionCount) {
            if (meta >= image.size()) fail("truncated import metadata");
            const Byte marker = image[meta++];
            if (marker == 0) {
                write64(image, thunk, 0);
                break;
            }
            if (marker == 1) {
                const std::string name = readAsciiZ(image, meta, image.size());
                meta += name.size() + 1;
                const std::uint64_t nameRva = read64(image, thunk);
                if (nameRva > std::numeric_limits<std::uint32_t>::max())
                    fail("bad import-name RVA");
                const std::size_t nameOff = imageOffset(
                    static_cast<std::uint32_t>(nameRva), firstRva, image.size(), "import name");
                copyAsciiZ(image, nameOff + 2, name);
            } else if (marker == 0xff) {
                const std::uint16_t ordinal = read16(image, meta);
                meta += 2;
                write64(image, thunk, (std::uint64_t{1} << 63) | ordinal);
            } else {
                fail("unsupported compact import marker " + std::to_string(marker));
            }
            thunk += 8;
            if (thunk + 8 > image.size()) fail("IAT exceeds decompressed image");
        }
        descriptor += 20;
    }
    fail("too many imported DLLs");
}

static std::vector<std::uint32_t> restoreRelocationsFromStub(Bytes &image,
                                                             const EmbeddedPe &pe,
                                                             std::uint32_t metadataRva) {
    const std::uint32_t firstRva = pe.sections.front().virtualAddress;
    std::size_t cursor = imageOffset(metadataRva, firstRva, image.size(), "relocation metadata");
    std::int64_t location = -4;
    std::vector<std::uint32_t> relocations;
    const std::uint64_t loadedBase = pe.imageBase + firstRva;

    for (std::size_t count = 0; count < image.size(); ++count) {
        if (cursor >= image.size()) fail("truncated relocation metadata");
        const Byte first = image[cursor++];
        if (first == 0) return relocations;

        std::uint32_t delta;
        if (first <= 0xef) {
            delta = first;
        } else {
            if (cursor + 2 > image.size()) fail("truncated long relocation delta");
            delta = (static_cast<std::uint32_t>(first & 0x0f) << 16) |
                    read16(image, cursor);
            cursor += 2;
        }
        location += delta;
        if (location < 0 || static_cast<std::uint64_t>(location) + 8 > image.size())
            fail("relocation target outside decompressed image");

        const std::size_t off = static_cast<std::size_t>(location);
        write64(image, off, readBe64(image, off) + loadedBase);
        relocations.push_back(firstRva + static_cast<std::uint32_t>(off));
    }
    fail("unterminated relocation metadata");
}

static void buildRelocationSection(Bytes &image,
                                   const EmbeddedPe &pe,
                                   const std::vector<std::uint32_t> &relocations) {
    const std::uint32_t firstRva = pe.sections.front().virtualAddress;
    const std::uint32_t relocRva = embeddedDirectoryRva(image, pe, 5);
    if (relocRva == 0 || relocations.empty()) return;

    const Section *relocSection = nullptr;
    for (const auto &section : pe.sections) {
        if (relocRva >= section.virtualAddress &&
            relocRva - section.virtualAddress < std::max(section.virtualSize, section.rawSize)) {
            relocSection = &section;
            break;
        }
    }
    if (!relocSection) fail("relocation directory has no section");
    const std::size_t sectionOff = imageOffset(
        relocSection->virtualAddress, firstRva, image.size(), "relocation section");
    if (sectionOff + relocSection->rawSize > image.size())
        fail("relocation section exceeds decompressed image");
    std::fill(image.begin() + sectionOff, image.begin() + sectionOff + relocSection->rawSize, 0);

    std::map<std::uint32_t, std::vector<std::uint16_t>> pages;
    for (std::uint32_t rva : relocations)
        pages[rva & ~0xfffu].push_back(static_cast<std::uint16_t>(0xa000u | (rva & 0xfffu)));

    std::size_t cursor = imageOffset(relocRva, firstRva, image.size(), "relocation directory");
    const std::size_t begin = cursor;
    for (auto &[page, entries] : pages) {
        if (entries.size() & 1u) entries.push_back(0);
        const std::uint32_t blockSize = 8 + static_cast<std::uint32_t>(entries.size() * 2);
        if (cursor + blockSize > image.size()) fail("rebuilt relocations exceed image");
        write32(image, cursor, page);
        write32(image, cursor + 4, blockSize);
        cursor += 8;
        for (std::uint16_t entry : entries) {
            write16(image, cursor, entry);
            cursor += 2;
        }
    }

    const std::uint32_t rebuiltSize = static_cast<std::uint32_t>(cursor - begin);
    write32(image, pe.dataDirectoryOffset + 5 * 8 + 4, rebuiltSize);
}

struct ResourceLeaf {
    std::size_t dataEntryOffset{};
    std::size_t packedDataOffset{};
    std::uint32_t originalRva{};
    std::uint32_t size{};
};

static void scanResourceDirectory(const Bytes &resource,
                                  std::size_t directoryOffset,
                                  std::uint32_t packedResourceRva,
                                  std::set<std::size_t> &visited,
                                  std::size_t &structureEnd,
                                  std::vector<ResourceLeaf> &leaves,
                                  unsigned depth) {
    if (depth > 16 || !visited.insert(directoryOffset).second)
        fail("cyclic or too-deep resource tree");
    if (directoryOffset + 16 > resource.size()) fail("resource directory outside section");
    const std::uint32_t count = static_cast<std::uint32_t>(read16(resource, directoryOffset + 12)) +
                                read16(resource, directoryOffset + 14);
    const std::size_t entriesEnd = directoryOffset + 16 + static_cast<std::size_t>(count) * 8;
    if (entriesEnd > resource.size()) fail("resource entries outside section");
    structureEnd = std::max(structureEnd, entriesEnd);

    for (std::uint32_t i = 0; i < count; ++i) {
        const std::size_t entry = directoryOffset + 16 + static_cast<std::size_t>(i) * 8;
        const std::uint32_t name = read32(resource, entry);
        const std::uint32_t child = read32(resource, entry + 4);
        if (name & 0x80000000u) {
            const std::size_t nameOff = name & 0x7fffffffu;
            const std::uint16_t length = read16(resource, nameOff);
            const std::size_t nameEnd = nameOff + 2 + static_cast<std::size_t>(length) * 2;
            if (nameEnd > resource.size()) fail("resource name outside section");
            structureEnd = std::max(structureEnd, nameEnd);
        }
        if (child & 0x80000000u) {
            scanResourceDirectory(resource, child & 0x7fffffffu, packedResourceRva,
                                  visited, structureEnd, leaves, depth + 1);
        } else {
            const std::size_t dataEntry = child;
            if (dataEntry + 16 > resource.size()) fail("resource data entry outside section");
            structureEnd = std::max(structureEnd, dataEntry + 16);
            const std::uint32_t dataRva = read32(resource, dataEntry);
            const std::uint32_t size = read32(resource, dataEntry + 4);
            if (dataRva < packedResourceRva) fail("resource data RVA precedes section");
            const std::size_t packedData = dataRva - packedResourceRva;
            if (packedData < 4 || packedData + size > resource.size())
                fail("resource payload outside section");
            const std::uint32_t originalRva = read32(resource, packedData - 4);
            leaves.push_back({dataEntry, packedData, originalRva, size});
        }
    }
}

static void rebuildResources(Bytes &image,
                             const EmbeddedPe &outPe,
                             const Bytes &packedFile,
                             const PeImage &packedPe) {
    const std::uint32_t outputRva = embeddedDirectoryRva(image, outPe, 2);
    const std::uint32_t packedRva = packedDirectoryRva(packedFile, packedPe, 2);
    if (outputRva == 0 || packedRva == 0) return;

    const std::uint32_t firstRva = outPe.sections.front().virtualAddress;
    const Section *packedSection = nullptr;
    for (const auto &section : packedPe.sections) {
        if (packedRva >= section.virtualAddress &&
            packedRva - section.virtualAddress < std::max(section.virtualSize, section.rawSize)) {
            packedSection = &section;
            break;
        }
    }
    const Section *outputSection = nullptr;
    for (const auto &section : outPe.sections) {
        if (outputRva >= section.virtualAddress &&
            outputRva - section.virtualAddress < std::max(section.virtualSize, section.rawSize)) {
            outputSection = &section;
            break;
        }
    }
    if (!packedSection || !outputSection) fail("resource directory has no section");
    if (packedSection->rawOffset + packedSection->rawSize > packedFile.size())
        fail("packed resource section is truncated");

    Bytes resource(packedFile.begin() + packedSection->rawOffset,
                   packedFile.begin() + packedSection->rawOffset + packedSection->rawSize);
    std::set<std::size_t> visited;
    std::vector<ResourceLeaf> leaves;
    std::size_t structureEnd = 0;
    scanResourceDirectory(resource, packedRva - packedSection->virtualAddress,
                          packedSection->virtualAddress, visited, structureEnd, leaves, 0);

    const std::size_t outputSectionOff = imageOffset(
        outputSection->virtualAddress, firstRva, image.size(), "resource section");
    if (outputSectionOff + outputSection->rawSize > image.size())
        fail("output resource section exceeds decompressed image");
    std::fill(image.begin() + outputSectionOff,
              image.begin() + outputSectionOff + outputSection->rawSize, 0);

    const std::size_t packedRoot = packedRva - packedSection->virtualAddress;
    const std::size_t outputRoot = imageOffset(outputRva, firstRva, image.size(), "resource root");
    if (packedRoot + structureEnd > resource.size() || outputRoot + structureEnd > image.size())
        fail("resource structure exceeds section");
    std::memcpy(image.data() + outputRoot, resource.data() + packedRoot, structureEnd);

    for (const auto &leaf : leaves) {
        const std::size_t relativeEntry = leaf.dataEntryOffset - packedRoot;
        write32(image, outputRoot + relativeEntry, leaf.originalRva);
        const std::size_t destination = imageOffset(
            leaf.originalRva, firstRva, image.size(), "resource payload");
        if (destination + leaf.size > image.size()) fail("resource payload exceeds output image");
        std::memcpy(image.data() + destination,
                    resource.data() + leaf.packedDataOffset,
                    leaf.size);
    }
}

static void restoreCanonicalDosMessage(Bytes &output, std::size_t peOffset) {
    static constexpr char message[] = "This program cannot be run in DOS mode.\r\r\n$";
    constexpr std::size_t messageOffset = 0x4e;
    if (peOffset >= messageOffset + sizeof(message) - 1) {
        std::fill(output.begin() + messageOffset,
                  output.begin() + std::min(peOffset, messageOffset + 48), 0);
        std::memcpy(output.data() + messageOffset, message, sizeof(message) - 1);
    }
}

static Bytes buildOutputPe(const Bytes &image,
                           const EmbeddedPe &outPe,
                           const Bytes &packedFile,
                           const PeImage &packedPe,
                           std::uint32_t expectedFileSize) {
    const std::uint32_t firstRva = outPe.sections.front().virtualAddress;
    std::size_t outputSectionsEnd = 0;
    for (const auto &section : outPe.sections)
        if (section.rawOffset && section.rawSize)
            outputSectionsEnd = std::max(outputSectionsEnd,
                                         static_cast<std::size_t>(section.rawOffset) + section.rawSize);

    const std::uint32_t packedFileAlignment = read32(packedFile, packedPe.optionalOffset + 36);
    std::size_t packedSectionsEnd = 0;
    for (const auto &section : packedPe.sections)
        if (section.rawOffset && section.rawSize)
            packedSectionsEnd = std::max(packedSectionsEnd,
                                         static_cast<std::size_t>(section.rawOffset) + section.rawSize);
    const std::size_t packedOverlay = alignUp(packedSectionsEnd, packedFileAlignment);
    if (packedOverlay > packedFile.size()) fail("packed overlay offset outside file");
    const std::size_t overlaySize = packedFile.size() - packedOverlay;
    const std::size_t computedSize = outputSectionsEnd + overlaySize;
    if (expectedFileSize != 0 && computedSize != expectedFileSize)
        fail("rebuilt file size does not match UPX metadata");

    Bytes output(computedSize, 0);
    if (packedPe.peOffset > packedFile.size() || packedPe.peOffset > output.size())
        fail("bad DOS stub size");
    std::memcpy(output.data(), packedFile.data(), packedPe.peOffset);
    restoreCanonicalDosMessage(output, packedPe.peOffset);

    const std::size_t headersToCopy = outPe.headerSize + outPe.sections.size() * 40;
    if (outPe.offset + headersToCopy > image.size() ||
        packedPe.peOffset + headersToCopy > output.size())
        fail("rebuilt PE headers exceed output");
    std::memcpy(output.data() + packedPe.peOffset,
                image.data() + outPe.offset,
                headersToCopy);

    for (const auto &section : outPe.sections) {
        if (section.rawOffset == 0 || section.rawSize == 0) continue;
        const std::size_t source = imageOffset(
            section.virtualAddress, firstRva, image.size(), "section data");
        if (source + section.rawSize > image.size() ||
            static_cast<std::size_t>(section.rawOffset) + section.rawSize > output.size())
            fail("section data exceeds buffer");
        std::memcpy(output.data() + section.rawOffset,
                    image.data() + source,
                    section.rawSize);
    }

    if (overlaySize)
        std::memcpy(output.data() + outputSectionsEnd,
                    packedFile.data() + packedOverlay,
                    overlaySize);
    return output;
}

int main(int argc, char **argv) {
    try {
        if (argc < 2 || argc > 3) {
            std::cerr << "usage: upx_patcher_unpacker <packed.exe> [unpacked.exe]\n";
            return 2;
        }

        const fs::path inputPath(argv[1]);
        const fs::path outputPath = argc == 3
                                        ? fs::path(argv[2])
                                        : inputPath.parent_path() /
                                              (inputPath.stem().string() + "-unpacked.exe");
        const Bytes packedFile = readFile(inputPath);
        const PeImage pe = parsePe(packedFile);
        const PackHeader ph = findPackHeader(packedFile, pe);
        const StubFacts stub = inspectStubBytes(packedFile, pe, ph.method, ph.filter);

        const std::size_t streamOffset = ph.offset + 32;
        Bytes image;
        if (ph.method == 2) {
            image = decompressNrv2bLe32FromStub(
                packedFile.data() + streamOffset, ph.packedSize, ph.unpackedSize);
        } else if (ph.method == 5) {
            image = decompressNrv2dLe32FromStub(
                packedFile.data() + streamOffset, ph.packedSize, ph.unpackedSize);
        } else if (ph.method == 8) {
            image = decompressNrv2eLe32FromStub(
                packedFile.data() + streamOffset, ph.packedSize, ph.unpackedSize);
        } else if (ph.method == 14) {
            image = decompressLzmaFromStub(
                packedFile.data() + streamOffset, ph.packedSize, ph.unpackedSize);
        } else {
            fail("unsupported compression method " + std::to_string(ph.method));
        }

        const std::uint32_t rawAdler = adler32(image);
        if (rawAdler != ph.unpackedAdler)
            fail("decompressed Adler-32 mismatch: got " + hex32(rawAdler) +
                 ", expected " + hex32(ph.unpackedAdler));

        EmbeddedPe embedded = parseEmbeddedPe(image);
        const std::uint32_t firstRva = embedded.sections.front().virtualAddress;
        if (stub.hasFilter &&
            (stub.filteredCodeSize != embedded.codeSize || stub.filterCto != ph.filterCto))
            fail("entry-stub immediates disagree with the recovered metadata");

        if (ph.filter == 0x49) {
            const std::size_t codeOffset = imageOffset(
                embedded.codeBase, firstRva, image.size(), "code section");
            unfilter49FromStub(image, codeOffset, embedded.codeSize, ph.filterCto);
        } else if (ph.filter != 0) {
            fail("unsupported stub filter " + std::to_string(ph.filter));
        }

        if (embedded.metadataOffset + 13 > image.size())
            fail("truncated post-image metadata");
        const std::uint32_t importMetadataOffset = read32(image, embedded.metadataOffset);
        const std::uint32_t namesAreaOffset = read32(image, embedded.metadataOffset + 4);
        if (namesAreaOffset != 0)
            fail("separate rebuilt import-name area is not implemented");
        const std::uint32_t relocationMetadataOffset = read32(image, embedded.metadataOffset + 8);

        rebuildImportsFromStub(image, embedded, packedFile, pe,
                               firstRva + importMetadataOffset);
        const auto relocations = restoreRelocationsFromStub(
            image, embedded, firstRva + relocationMetadataOffset);
        buildRelocationSection(image, embedded, relocations);
        rebuildResources(image, embedded, packedFile, pe);

        const std::size_t embeddedOptional = embedded.offset + 24;
        write32(image, embeddedOptional + 64, 0);
        write32(image, embedded.dataDirectoryOffset + 12 * 8, 0);
        write32(image, embedded.dataDirectoryOffset + 12 * 8 + 4, 0);

        const Bytes output = buildOutputPe(
            image, embedded, packedFile, pe, ph.originalFileSize);

        writeFile(outputPath, output);
        std::cout << "Recovered UPX header at file offset 0x" << std::hex << ph.offset
                  << std::dec << " (version " << static_cast<unsigned>(ph.version)
                  << ", method " << static_cast<unsigned>(ph.method)
                  << ", filter 0x" << std::hex << static_cast<unsigned>(ph.filter)
                  << std::dec << ")\n";
        std::cout << "Static unpack: " << packedFile.size() << " -> " << output.size()
                  << " bytes, " << relocations.size() << " DIR64 relocations\n";
        std::cout << "Wrote " << outputPath.string() << "\n";
        return 0;
    } catch (const std::exception &e) {
        std::cerr << "error: " << e.what() << '\n';
        return 1;
    }
}
