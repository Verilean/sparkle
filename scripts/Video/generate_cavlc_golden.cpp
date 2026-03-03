/*
 * H.264 CAVLC Golden Reference — Generates bit-accurate encoding
 *
 * Implements Context-Adaptive Variable-Length Coding for H.264 Baseline Profile.
 * Encodes a 4x4 block of quantized transform coefficients using the nC=0 tables.
 *
 * Reference: ITU-T H.264 (03/2005), Section 9.2.1
 *
 * Usage:
 *   g++ -std=c++17 -o generate_cavlc_golden Scripts/Video/generate_cavlc_golden.cpp
 *   ./generate_cavlc_golden
 */

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cassert>
#include <vector>

// ============================================================================
// Bitstream writer
// ============================================================================

struct BitstreamWriter {
    uint32_t buffer = 0;
    int bitPos = 0;  // next bit position (MSB-first packing)

    void writeBits(uint32_t code, int len) {
        assert(len > 0 && len <= 32);
        assert(bitPos + len <= 32);
        // Pack MSB-first: the first bit written goes to the highest position
        buffer |= (code << (32 - bitPos - len));
        bitPos += len;
    }

    void print() const {
        printf("  bitstream (hex): 0x%08X\n", buffer);
        printf("  bitstream (bin): ");
        for (int i = 0; i < bitPos; i++) {
            printf("%d", (buffer >> (31 - i)) & 1);
        }
        printf("\n");
        printf("  total bits: %d\n", bitPos);
    }
};

// ============================================================================
// Zig-zag scan table for 4x4 blocks (H.264 Table 8-13, frame scan)
// Maps scan position → raster position
// ============================================================================

static const int zigzag4x4[16] = {
    0,  1,  4,  8,
    5,  2,  3,  6,
    9,  12, 13, 10,
    7,  11, 14, 15
};

// ============================================================================
// coeff_token VLC table for 0 ≤ nC < 2 (H.264 Table 9-5a)
// Indexed as [totalCoeff][trailingOnes] = {code, length}
// ============================================================================

struct VLC {
    uint32_t code;
    int length;
};

// Table 9-5(a): 0 ≤ nC < 2
// Rows: totalCoeff 0..16, Columns: trailingOnes 0..3
static const VLC coeff_token_nC0[17][4] = {
    // TC=0
    {{1, 1},   {0, 0},   {0, 0},   {0, 0}},
    // TC=1
    {{5, 6},   {1, 2},   {0, 0},   {0, 0}},
    // TC=2
    {{7, 8},   {4, 6},   {1, 3},   {0, 0}},
    // TC=3
    {{7, 9},   {3, 7},   {3, 5},   {2, 5}},
    // TC=4
    {{7, 10},  {6, 8},   {2, 7},   {3, 6}},
    // TC=5
    {{7, 11},  {6, 9},   {5, 8},   {4, 7}},
    // TC=6
    {{15, 13}, {5, 9},   {4, 9},   {4, 8}},
    // TC=7
    {{11, 13}, {7, 11},  {6, 9},   {5, 8}},
    // TC=8
    {{8, 13},  {9, 11},  {8, 9},   {6, 8}},
    // TC=9
    {{15, 14}, {11, 11}, {10, 9},  {9, 9}},
    // TC=10
    {{11, 14}, {8, 11},  {12, 10}, {8, 9}},
    // TC=11
    {{15, 15}, {13, 12}, {12, 10}, {10, 9}},
    // TC=12
    {{11, 15}, {10, 12}, {14, 10}, {12, 9}},
    // TC=13
    {{15, 16}, {14, 13}, {13, 10}, {14, 9}},
    // TC=14
    {{11, 16}, {10, 13}, {9, 10},  {11, 9}},
    // TC=15
    {{7, 16},  {6, 13},  {5, 10},  {13, 9}},
    // TC=16
    {{3, 16},  {2, 13},  {1, 10},  {1, 9}},
};

// ============================================================================
// total_zeros VLC tables (H.264 Table 9-7)
// Indexed as [totalCoeff-1][totalZeros] = {code, length}
// Only need totalCoeff=1..15 (16 has no zeros possible)
// ============================================================================

// Table 9-7a: totalCoeff=1
static const VLC total_zeros_tc1[] = {
    {1, 1},   // tz=0
    {3, 3},   // tz=1
    {2, 3},   // tz=2
    {3, 4},   // tz=3
    {2, 4},   // tz=4
    {3, 5},   // tz=5
    {2, 5},   // tz=6
    {3, 6},   // tz=7
    {2, 6},   // tz=8
    {3, 7},   // tz=9
    {2, 7},   // tz=10
    {3, 8},   // tz=11
    {2, 8},   // tz=12
    {3, 9},   // tz=13
    {2, 9},   // tz=14
    {1, 9},   // tz=15
};

// Table 9-7b: totalCoeff=2
static const VLC total_zeros_tc2[] = {
    {7, 3},   // tz=0
    {6, 3},   // tz=1
    {5, 3},   // tz=2
    {4, 3},   // tz=3
    {3, 3},   // tz=4
    {5, 4},   // tz=5
    {4, 4},   // tz=6
    {3, 4},   // tz=7
    {2, 4},   // tz=8
    {3, 5},   // tz=9
    {2, 5},   // tz=10
    {3, 6},   // tz=11
    {2, 6},   // tz=12
    {1, 6},   // tz=13
    {0, 6},   // tz=14
};

// Table 9-7c: totalCoeff=3
static const VLC total_zeros_tc3[] = {
    {5, 4},   // tz=0
    {7, 3},   // tz=1
    {6, 3},   // tz=2
    {5, 3},   // tz=3
    {4, 3},   // tz=4
    {3, 3},   // tz=5
    {4, 4},   // tz=6
    {3, 4},   // tz=7
    {2, 4},   // tz=8
    {3, 5},   // tz=9
    {2, 5},   // tz=10
    {1, 6},   // tz=11
    {1, 5},   // tz=12
    {0, 6},   // tz=13
};

// Table 9-7d: totalCoeff=4
static const VLC total_zeros_tc4[] = {
    {3, 5},   // tz=0
    {7, 3},   // tz=1
    {5, 4},   // tz=2
    {4, 4},   // tz=3
    {6, 3},   // tz=4
    {5, 3},   // tz=5
    {4, 3},   // tz=6
    {3, 3},   // tz=7
    {3, 4},   // tz=8
    {2, 4},   // tz=9
    {2, 5},   // tz=10
    {1, 5},   // tz=11
    {0, 5},   // tz=12
};

// Table 9-7e: totalCoeff=5
static const VLC total_zeros_tc5[] = {
    {5, 4},   // tz=0
    {4, 4},   // tz=1
    {3, 4},   // tz=2
    {7, 3},   // tz=3
    {6, 3},   // tz=4
    {5, 3},   // tz=5
    {4, 3},   // tz=6
    {3, 3},   // tz=7
    {2, 4},   // tz=8
    {1, 5},   // tz=9
    {1, 4},   // tz=10
    {0, 5},   // tz=11
};

// Table 9-7f: totalCoeff=6
static const VLC total_zeros_tc6[] = {
    {1, 6},   // tz=0
    {1, 5},   // tz=1
    {7, 3},   // tz=2
    {6, 3},   // tz=3
    {5, 3},   // tz=4
    {4, 3},   // tz=5
    {3, 3},   // tz=6
    {2, 3},   // tz=7
    {1, 4},   // tz=8
    {1, 3},   // tz=9
    {0, 6},   // tz=10
};

// Simplified: only implement up to totalCoeff=6 for the tables
// (our test case has totalCoeff=3, so this is sufficient)

struct TotalZerosTable {
    const VLC* entries;
    int maxZeros;
};

static const TotalZerosTable total_zeros_tables[] = {
    {nullptr, 0},        // index 0 unused (TC=0 has no total_zeros)
    {total_zeros_tc1, 15},
    {total_zeros_tc2, 14},
    {total_zeros_tc3, 13},
    {total_zeros_tc4, 12},
    {total_zeros_tc5, 11},
    {total_zeros_tc6, 10},
};

// ============================================================================
// run_before VLC table (H.264 Table 9-10)
// Indexed as [zerosLeft-1][runBefore] = {code, length}
// ============================================================================

static const VLC run_before_zl1[] = {
    {1, 1},   // rb=0
    {0, 1},   // rb=1
};

static const VLC run_before_zl2[] = {
    {1, 1},   // rb=0
    {1, 2},   // rb=1
    {0, 2},   // rb=2
};

static const VLC run_before_zl3[] = {
    {3, 2},   // rb=0
    {2, 2},   // rb=1
    {1, 2},   // rb=2
    {0, 2},   // rb=3
};

static const VLC run_before_zl4[] = {
    {3, 2},   // rb=0
    {2, 2},   // rb=1
    {1, 2},   // rb=2
    {1, 3},   // rb=3
    {0, 3},   // rb=4
};

static const VLC run_before_zl5[] = {
    {3, 2},   // rb=0
    {2, 2},   // rb=1
    {3, 3},   // rb=2
    {2, 3},   // rb=3
    {1, 3},   // rb=4
    {0, 3},   // rb=5
};

static const VLC run_before_zl6[] = {
    {3, 2},   // rb=0
    {0, 3},   // rb=1
    {1, 3},   // rb=2
    {3, 3},   // rb=3
    {2, 3},   // rb=4
    {5, 3},   // rb=5
    {4, 3},   // rb=6
};

static const VLC run_before_zl7plus[] = {
    {7, 3},   // rb=0
    {6, 3},   // rb=1
    {5, 3},   // rb=2
    {4, 3},   // rb=3
    {3, 3},   // rb=4
    {2, 3},   // rb=5
    {1, 3},   // rb=6
    {1, 4},   // rb=7
    {1, 5},   // rb=8
    {1, 6},   // rb=9
    {1, 7},   // rb=10
    {1, 8},   // rb=11
    {1, 9},   // rb=12
    {1, 10},  // rb=13
    {1, 11},  // rb=14
    {1, 12},  // rb=15
};

struct RunBeforeTable {
    const VLC* entries;
    int maxRun;
};

static const RunBeforeTable run_before_tables[] = {
    {nullptr, 0},            // index 0 unused
    {run_before_zl1, 1},    // zerosLeft=1
    {run_before_zl2, 2},    // zerosLeft=2
    {run_before_zl3, 3},    // zerosLeft=3
    {run_before_zl4, 4},    // zerosLeft=4
    {run_before_zl5, 5},    // zerosLeft=5
    {run_before_zl6, 6},    // zerosLeft=6
    {run_before_zl7plus, 15}, // zerosLeft >= 7
};

static VLC lookupRunBefore(int zerosLeft, int runBefore) {
    int idx = (zerosLeft >= 7) ? 7 : zerosLeft;
    assert(idx >= 1 && runBefore >= 0);
    return run_before_tables[idx].entries[runBefore];
}

// ============================================================================
// Level encoding (H.264 Section 9.2.2.1)
// ============================================================================

static void encodeLevel(BitstreamWriter& bs, int level, int& suffixLength,
                        bool isFirst, int trailingOnes) {
    // Compute level code
    int levelCode;
    if (level > 0)
        levelCode = 2 * level - 2;
    else
        levelCode = -2 * level - 1;

    // If first level after trailing ones and T1 < 3, adjust
    if (isFirst && trailingOnes < 3) {
        levelCode -= 2;
    }

    printf("    level=%d, levelCode=%d, suffixLength=%d\n", level, levelCode, suffixLength);

    // Determine prefix and suffix
    int levelPrefix, levelSuffix, levelSuffixSize;

    if (suffixLength == 0) {
        if (levelCode < 14) {
            levelPrefix = levelCode;
            levelSuffixSize = 0;
            levelSuffix = 0;
        } else if (levelCode < 30) {
            levelPrefix = 14;
            levelSuffixSize = 4;
            levelSuffix = levelCode - 14;
        } else {
            levelPrefix = 15;
            levelSuffixSize = 12;
            levelSuffix = levelCode - 15;
        }
    } else {
        levelPrefix = levelCode >> suffixLength;
        levelSuffixSize = suffixLength;
        levelSuffix = levelCode - (levelPrefix << suffixLength);
        if (levelPrefix >= 15) {
            // Escape code
            levelPrefix = 15;
            levelSuffixSize = 12;
            levelSuffix = levelCode - (15 << suffixLength);
        }
    }

    printf("    prefix=%d, suffixSize=%d, suffix=%d\n",
           levelPrefix, levelSuffixSize, levelSuffix);

    // Write prefix: levelPrefix zeros followed by 1
    int prefixBits = levelPrefix + 1;
    bs.writeBits(1, prefixBits);  // levelPrefix zeros + 1

    // Write suffix
    if (levelSuffixSize > 0) {
        bs.writeBits(levelSuffix, levelSuffixSize);
    }

    // Update suffixLength
    if (suffixLength == 0) {
        suffixLength = 1;
    }
    int absLevel = (level > 0) ? level : -level;
    if (absLevel > (3 << (suffixLength - 1)) && suffixLength < 6) {
        suffixLength++;
    }
}

// ============================================================================
// Main: CAVLC encode a test block
// ============================================================================

int main() {
    // Test block in raster order
    int16_t block[16] = {0, 3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

    printf("=== H.264 CAVLC Golden Reference ===\n\n");

    // Step 1: Zig-zag scan
    int16_t scanned[16];
    printf("Zig-zag scan:\n");
    for (int i = 0; i < 16; i++) {
        scanned[i] = block[zigzag4x4[i]];
        printf("  scan[%2d] = block[%2d] = %d\n", i, zigzag4x4[i], scanned[i]);
    }
    printf("\n");

    // Step 2: Analyze coefficients
    int totalCoeff = 0;
    int trailingOnes = 0;
    int totalZeros = 0;
    int lastNzPos = -1;
    int t1Signs[3] = {0, 0, 0};  // signs of trailing ones (0=positive, 1=negative)

    // Count non-zeros and find last non-zero position
    for (int i = 0; i < 16; i++) {
        if (scanned[i] != 0) {
            totalCoeff++;
            lastNzPos = i;
        }
    }

    // Count zeros between position 0 and last non-zero
    if (totalCoeff > 0) {
        totalZeros = (lastNzPos + 1) - totalCoeff;
    }

    // Find trailing ones (scan backward from last non-zero)
    // Trailing ones are consecutive ±1 values at the highest-frequency end
    trailingOnes = 0;
    {
        int nzCount = 0;
        for (int i = lastNzPos; i >= 0 && trailingOnes < 3; i--) {
            if (scanned[i] != 0) {
                if (scanned[i] == 1 || scanned[i] == -1) {
                    t1Signs[trailingOnes] = (scanned[i] < 0) ? 1 : 0;
                    trailingOnes++;
                } else {
                    break;
                }
            }
        }
    }

    printf("Analysis:\n");
    printf("  totalCoeff   = %d\n", totalCoeff);
    printf("  trailingOnes = %d\n", trailingOnes);
    printf("  totalZeros   = %d\n", totalZeros);
    printf("  lastNzPos    = %d\n", lastNzPos);
    printf("  T1 signs     = ");
    for (int i = 0; i < trailingOnes; i++) printf("%d ", t1Signs[i]);
    printf("\n\n");

    // Collect non-zero levels in reverse scan order (excluding trailing ones)
    std::vector<int> levels;
    {
        int skipT1 = trailingOnes;
        for (int i = lastNzPos; i >= 0; i--) {
            if (scanned[i] != 0) {
                if (skipT1 > 0) {
                    skipT1--;
                } else {
                    levels.push_back(scanned[i]);
                }
            }
        }
    }

    printf("Levels (reverse scan order, excl T1): ");
    for (int l : levels) printf("%d ", l);
    printf("\n");

    // Collect run_before values (for each non-zero in reverse scan order)
    // run_before[i] = number of zeros between the i-th non-zero (from high freq)
    // and the (i+1)-th non-zero
    std::vector<int> runBefore;
    {
        // Positions of non-zero coefficients in scan order
        std::vector<int> nzPositions;
        for (int i = 0; i <= lastNzPos; i++) {
            if (scanned[i] != 0) {
                nzPositions.push_back(i);
            }
        }
        // In reverse order: nzPositions[totalCoeff-1] is highest freq
        // run_before for the i-th non-zero (reverse) = gap to the next non-zero
        for (int i = (int)nzPositions.size() - 1; i > 0; i--) {
            int gap = nzPositions[i] - nzPositions[i-1] - 1;
            runBefore.push_back(gap);
        }
        // Last run_before is inferred (not coded)
    }

    printf("Run-before values: ");
    for (int r : runBefore) printf("%d ", r);
    printf("\n\n");

    // Step 3: Encode
    BitstreamWriter bs;

    // 3a. coeff_token
    if (totalCoeff == 0) {
        VLC ct = coeff_token_nC0[0][0];
        printf("coeff_token: TC=%d, T1=%d → code=%d, len=%d\n",
               totalCoeff, trailingOnes, ct.code, ct.length);
        bs.writeBits(ct.code, ct.length);
    } else {
        VLC ct = coeff_token_nC0[totalCoeff][trailingOnes];
        printf("coeff_token: TC=%d, T1=%d → code=0x%X (%d), len=%d\n",
               totalCoeff, trailingOnes, ct.code, ct.code, ct.length);
        bs.writeBits(ct.code, ct.length);

        // 3b. trailing_ones_sign_flag
        printf("trailing_ones_sign_flag: ");
        for (int i = 0; i < trailingOnes; i++) {
            printf("%d ", t1Signs[i]);
            bs.writeBits(t1Signs[i], 1);
        }
        printf("\n");

        // 3c. Levels
        if (!levels.empty()) {
            printf("Level encoding:\n");
            int suffixLength = 0;
            if (totalCoeff > 10 && trailingOnes < 3) {
                suffixLength = 1;
            }
            for (int i = 0; i < (int)levels.size(); i++) {
                encodeLevel(bs, levels[i], suffixLength, (i == 0), trailingOnes);
            }
        }

        // 3d. total_zeros
        if (totalCoeff < 16) {
            assert(totalCoeff >= 1 && totalCoeff <= (int)(sizeof(total_zeros_tables)/sizeof(total_zeros_tables[0])) - 1);
            VLC tz = total_zeros_tables[totalCoeff].entries[totalZeros];
            printf("total_zeros: TC=%d, TZ=%d → code=%d, len=%d\n",
                   totalCoeff, totalZeros, tz.code, tz.length);
            bs.writeBits(tz.code, tz.length);
        }

        // 3e. run_before
        if (totalZeros > 0) {
            printf("run_before encoding:\n");
            int zerosLeft = totalZeros;
            for (int i = 0; i < (int)runBefore.size() && zerosLeft > 0; i++) {
                VLC rb = lookupRunBefore(zerosLeft, runBefore[i]);
                printf("  zerosLeft=%d, runBefore=%d → code=%d, len=%d\n",
                       zerosLeft, runBefore[i], rb.code, rb.length);
                bs.writeBits(rb.code, rb.length);
                zerosLeft -= runBefore[i];
            }
        }
    }

    printf("\n=== Final Bitstream ===\n");
    bs.print();

    // Print as Lean-compatible constants
    printf("\n=== Lean Constants ===\n");
    printf("  goldenBitstream : BitVec 32 := 0x%08X#32\n", bs.buffer);
    printf("  goldenBitLen    : BitVec 6  := %d#6\n", bs.bitPos);

    return 0;
}
