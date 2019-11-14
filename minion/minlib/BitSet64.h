//
// Created by lee on 2019/11/11.
//

#ifndef MINIONPROJECT_BITSET64_H
#define MINIONPROJECT_BITSET64_H

#include <vector>
#include <cmath>
#include <sstream>
#include <numeric>

namespace CTRL {
    std::vector<int> kk;
    typedef unsigned long long u64;

    inline int BitCount(const int a) {
        return __builtin_popcount(a);
    };

    inline int BitCount64(const u64 a) {
        return __builtin_popcountll(a);
    };

    inline int CLZ64(const u64 a) {
        return __builtin_clzll(a);
    };

    inline int CTZ64(const u64 a) {
        return __builtin_ctzll(a);
    };

    inline int FFS64(const u64 a) {
        return __builtin_ffsll(a);
    }

    inline void FLP(const u64 &a) {
        __builtin_bswap64(a);
    }

    const int kIndexOverflow = -1;
    const int kBitSize = 64;
    const int kDivBit = 6;
    const int kModMask = 0x3f;
    const int kIntMax = 0x3f3f3f3f;
    const u64 kAllOneLong = 0xFFFFFFFFFFFFFFFFL;

    class Index2D {
    public:
        int x, y;
    };

    inline Index2D GetIndex2D(const int index) {
        return Index2D{index >> kDivBit, index & kModMask};
    }

    inline int GetIndex(const Index2D &index2D) {
        return (index2D.x << kDivBit) + index2D.y;
    }



///* a=target variable, b=bit number to act upon 0-n */
#define BIT_SET(a, b) ((a) |= (1ULL<<(b)))
#define BIT_RESET(a, b) ((a) &= ~(1ULL<<(b)))
#define BIT_FLIP(a, b) ((a) ^= (1ULL<<(b)))
#define BIT_CHECK(a, b) ((a >> b) & 1ULL)

    class BitSet64 {

    private:
        std::vector<u64> words_;
        u64 last_mask_;
        int limit_;
        int bit_size_;
        int byte_size_;
        int int_size_;
        int long_size_;

        static const u64 kAllOne = 0xFFFFFFFFFFFFFFFFL;

    public:
        BitSet64() {};

        BitSet64(const int size) :
                bit_size_(size),
                byte_size_(static_cast<int>(ceilf(static_cast<float>(size) / 8))),
                int_size_(static_cast<int>(ceilf(static_cast<float>(size) / 32))),
                long_size_(static_cast<int>(ceilf(static_cast<float>(size) / 64))),
                limit_(size % kBitSize) {
            last_mask_ = kAllOne >> 64 - limit_;
            words_.resize(long_size_, 0);
        }

        void Resize(const int size) {
            bit_size_ = size;
            byte_size_ = static_cast<int>(ceilf(static_cast<float>(size) / 8));
            int_size_ = static_cast<int>(ceilf(static_cast<float>(size) / 32));
            long_size_ = static_cast<int>(ceilf(static_cast<float>(size) / 64));
            limit_ = bit_size_ % kBitSize;
            last_mask_ = kAllOne >> 64 - limit_;
            words_.resize(long_size_, 0);
        }

        int BitSize() const noexcept {
            return bit_size_;
        }

        int ByteSize() const noexcept {
            return byte_size_;
        }

        int IntSize() const noexcept {
            return int_size_;
        }

        int LongSize() const noexcept {
            return long_size_;
        }

        void Flip() noexcept {
            for (auto &w:words_) {
                w = ~w;
            }
            words_.back() &= last_mask_;
        }

        void Flip(const int i) noexcept {
            const Index2D p = GetIndex2D(i);
            BIT_FLIP(words_[p.x], p.y);
        }

        void Set(const int i) noexcept {
            const Index2D p = GetIndex2D(i);
            BIT_SET(words_[p.x], p.y);
        }

        void Set() noexcept {
            for (auto &w:words_) {
                w = kAllOne;
            }
            words_.back() = last_mask_;
        }

        void Set(BitSet64 &s) noexcept {
            for (int i = 0, len = long_size_; i < long_size_; ++i) {
                words_[i] = s.words_[i];
            }
        }

        void Reset() noexcept {
            for (auto &w:words_) {
                w = 0L;
            }
        }

        void Reset(const int i) noexcept {
            const Index2D p = GetIndex2D(i);
            BIT_RESET(words_[p.x], p.y);
        }

        void Reset(BitSet64 &s) noexcept {
            for (int i = 0, len = long_size_; i < long_size_; ++i) {
                words_[i] = ~s.words_[i];
            }
        }

        bool Empty() noexcept {
            for (auto w:words_) {
                if (w != 0L) {
                    return false;
                }
            }

            return true;
        }

        bool Check(const int i) noexcept {
            const Index2D p = GetIndex2D(i);
            return BIT_CHECK(words_[p.x], p.y);
        }

        int Count() noexcept {
            int sum = 0;
            for (auto w:words_) {
                sum += BitCount64(w);
            }
            return sum;
//            return std::accumulate(words_.begin(), words_.end(), 0, [](int a, u64 b) { return a + BitCount64(b); });
        }

        BitSet64 &operator&=(const BitSet64 &rhs) noexcept {
            for (int i = 0; i < long_size_; ++i) {
                words_[i] &= rhs.words_[i];
            }
            return *this;
        }

        BitSet64 &operator|=(const BitSet64 &rhs) noexcept {
            for (int i = 0; i < long_size_; ++i) {
                words_[i] |= rhs.words_[i];
            }
            return *this;
        }

        BitSet64 &operator^=(const BitSet64 &rhs) noexcept {
            for (int i = 0; i < long_size_; ++i) {
                words_[i] ^= rhs.words_[i];
            }
            words_.back() &= last_mask_;
            return *this;
        }

        bool operator==(const BitSet64 &rhs) noexcept {
            for (int i = 0; i < long_size_; ++i) {
                if (words_[i] != rhs.words_[i]) {
                    return false;
                }
            }
            return true;
        }

        bool operator!=(const BitSet64 &rhs) noexcept {
            for (int i = 0; i < long_size_; ++i) {
                if (words_[i] != rhs.words_[i]) {
                    return true;
                }
            }
            return false;
        }

        // 从ith(含ith)开始第一个为1的位的索引
        // 若没有返回-1
        int NextOneBit(const int i) noexcept {
            if (i >= bit_size_) {
                return kIndexOverflow;
            }

            Index2D p = GetIndex2D(i);
            u64 word = words_[p.x] & (kAllOne << p.y);
            while (true) {
                if (word != 0L)
                    return (p.x << kDivBit) + CTZ64(word);
                if (++p.x == long_size_)
                    return kIndexOverflow;
                word = words_[p.x];
            }
        }

        // 从ith(含ith)开始第一个为0的位的索引
        // 若没有返回-1
        int NextZeroBit(const int i) noexcept {
            if (i >= bit_size_) {
                return kIndexOverflow;
            }

            Index2D p = GetIndex2D(i);
            u64 word = ~words_[p.x] & (kAllOne << p.y);
            while (true) {
                if (word != 0L) {
                    const int i = (p.x << kDivBit) + CTZ64(word);
                    return i < bit_size_ ? i : kIndexOverflow;
                }
                if (++p.x == long_size_)
                    return kIndexOverflow;
                word = ~words_[p.x];
            }
        }

        std::string ToBitString() noexcept {
            std::string tmp_str_;

            for (int i = 0; i < bit_size_; ++i) {
                tmp_str_.push_back(Check(i) ? '1' : '0');
            }

            return tmp_str_;
        }

        std::vector<int> ToArray() noexcept {
            std::vector<int> indices(bit_size_);
            indices.clear();
            int i = NextOneBit(0);
            while (i != kIndexOverflow) {
                indices.push_back(i);
                i = NextOneBit(i + 1);
            }

            return indices;
        }

        const std::string ToString() noexcept {
            std::vector<int> indices(bit_size_);
            indices.clear();

            int i = NextOneBit(0);
            while (i != kIndexOverflow) {
                indices.push_back(i);
                i = NextOneBit(i + 1);
            }

            std::stringstream ss;
            ss << "{";
            for (auto a:indices) {
                ss << a;
                ss << ' ';
            }
            ss << "}";
            const std::string s = ss.str();

            return s;
        }

        static inline void BitAnd(BitSet64 &res, const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] & b.words_[i];
            }
        }

        static inline void BitOr(BitSet64 &res, const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] | b.words_[i];
            }
        }

        static inline void BitXor(BitSet64 &res, const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] ^ b.words_[i];
            }
        }

        static inline void
        BitAnd(BitSet64 &res, const BitSet64 &a, const BitSet64 &b, const BitSet64 &c, const BitSet64 &d) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] & b.words_[i] & c.words_[i] & d.words_[i];
            }
        }

        static inline void
        BitOr(BitSet64 &res, const BitSet64 &a, const BitSet64 &b, const BitSet64 &c, const BitSet64 &d) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] | b.words_[i] | c.words_[i] | d.words_[i];
            }
        }

        static inline void
        BitXor(BitSet64 &res, const BitSet64 &a, const BitSet64 &b, const BitSet64 &c, const BitSet64 &d) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                res.words_[i] = a.words_[i] ^ b.words_[i] ^ c.words_[i] ^ d.words_[i];
            }
        }

        static inline bool EmptyAnd(const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                if (a.words_[i] & b.words_[i] != 0L) {
                    return false;
                }
            }
            return true;
        }

        static inline bool EmptyOr(const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                if (a.words_[i] | b.words_[i] != 0L) {
                    return false;
                }
            }
            return true;
        }

        static inline bool EmptyXor(const BitSet64 &a, const BitSet64 &b) noexcept {
            for (int i = 0; i < a.long_size_; ++i) {
                if (a.words_[i] ^ b.words_[i] != 0L) {
                    return false;
                }
            }
            return true;
        }
    };
}


#endif //MINIONPROJECT_BITSET64_H
