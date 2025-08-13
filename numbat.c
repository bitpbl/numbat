#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <ctype.h>
#include <sys/types.h>

#ifndef NB_INLINE
# if defined(__GNUC__)
#  define NB_INLINE static inline __attribute__((always_inline))
# else
#  define NB_INLINE static inline
# endif
#endif

typedef struct {
    uint8_t signs;      // bit0: mantissa sign, bit1: exponent sign
    // mantissa
    uint8_t *mantissa;  // big-endian magnitude
    size_t m_len;       // allocated buffer length in bytes
    size_t m_used;      // bytes used (0 => zero)
    // exponent (magnitude)
    uint8_t *exponent;  // big-endian magnitude
    size_t e_len;
    size_t e_used;      // bytes used (0 => zero exponent)
} nb_t;

#define NB_MANT_POS_MASK  (1u<<0)
#define NB_EXP_POS_MASK   (1u<<1)

NB_INLINE int nb_mantissa_positive(const nb_t *n)  { return (n->signs & NB_MANT_POS_MASK) != 0; }
NB_INLINE int nb_exponent_positive(const nb_t *n)  { return (n->signs & NB_EXP_POS_MASK) != 0; }
NB_INLINE void nb_set_mantissa_positive(nb_t *n, int pos) { if (pos) n->signs |= NB_MANT_POS_MASK; else n->signs &= ~NB_MANT_POS_MASK; }
NB_INLINE void nb_set_exponent_positive(nb_t *n, int pos) { if (pos) n->signs |= NB_EXP_POS_MASK; else n->signs &= ~NB_EXP_POS_MASK; }

static int nb_ensure_mbuf(nb_t *n, size_t bytes) {
    if (n->m_len >= bytes) return 1;
    uint8_t *b = (uint8_t*)malloc(bytes);
    if (!b) return 0;
    memset(b, 0, bytes);
    // if existing used bytes, copy them to end
    if (n->mantissa && n->m_used) {
        size_t old_off = n->m_len - n->m_used;
        size_t new_off = bytes - n->m_used;
        memcpy(b + new_off, n->mantissa + old_off, n->m_used);
    }
    if (n->mantissa) free(n->mantissa);
    n->mantissa = b;
    n->m_len = bytes;
    return 1;
}

// ensure buffer for exponent
static int nb_ensure_ebuf(nb_t *n, size_t bytes) {
    if (n->e_len >= bytes) return 1;
    uint8_t *b = (uint8_t*)malloc(bytes);
    if (!b) return 0;
    memset(b, 0, bytes);
    if (n->exponent && n->e_used) {
        size_t old_off = n->e_len - n->e_used;
        size_t new_off = bytes - n->e_used;
        memcpy(b + new_off, n->exponent + old_off, n->e_used);
    }
    if (n->exponent) free(n->exponent);
    n->exponent = b;
    n->e_len = bytes;
    return 1;
}

nb_t *nb_new(void) {
    nb_t *n = (nb_t*)malloc(sizeof(nb_t));
    if (!n) return NULL;
    n->signs = NB_MANT_POS_MASK | NB_EXP_POS_MASK; // positive mantissa & exponent by default
    n->mantissa = NULL; n->m_len = 0; n->m_used = 0;
    n->exponent = NULL; n->e_len = 0; n->e_used = 0;
    return n;
}

void nb_free(nb_t *n) {
    if (!n) return;
    if (n->mantissa) free(n->mantissa);
    if (n->exponent) free(n->exponent);
    free(n);
}

void nb_normalize(nb_t *n) {
    if (!n) return;
    // mantissa
    if (n->m_used == 0) {
        if (n->mantissa) { free(n->mantissa); n->mantissa = NULL; n->m_len = 0; }
        nb_set_mantissa_positive(n, 1);
    } else {
        size_t off = n->m_len - n->m_used;
        size_t i = 0;
        while (i < n->m_used && n->mantissa[off + i] == 0) i++;
        if (i > 0) {
            n->m_used -= i;
            if (n->m_used == 0) {
                free(n->mantissa);
                n->mantissa = NULL;
                n->m_len = 0;
                nb_set_mantissa_positive(n, 1);
            } else {
                // move to end
                memmove(n->mantissa + (n->m_len - n->m_used), n->mantissa + off + i, n->m_used);
            }
        }
    }
    // exponent
    if (n->e_used == 0) {
        if (n->exponent) { free(n->exponent); n->exponent = NULL; n->e_len = 0; }
        nb_set_exponent_positive(n, 1);
    } else {
        size_t off = n->e_len - n->e_used;
        size_t i = 0;
        while (i < n->e_used && n->exponent[off + i] == 0) i++;
        if (i > 0) {
            n->e_used -= i;
            if (n->e_used == 0) {
                free(n->exponent);
                n->exponent = NULL;
                n->e_len = 0;
                nb_set_exponent_positive(n, 1);
            } else {
                memmove(n->exponent + (n->e_len - n->e_used), n->exponent + off + i, n->e_used);
            }
        }
    }
}

int nb_set_mantissa_bytes(nb_t *n, const uint8_t *bytes, size_t len, int positive) {
    if (!n) return 0;
    if (!bytes || len == 0) {
        if (n->mantissa) { free(n->mantissa); n->mantissa = NULL; n->m_len = 0; }
        n->m_used = 0;
        nb_set_mantissa_positive(n, 1);
        return 1;
    }

    size_t i = 0;
    while (i < len && bytes[i] == 0) i++;
    if (i == len) {
        if (n->mantissa) { free(n->mantissa); n->mantissa = NULL; n->m_len = 0; }
        n->m_used = 0;
        nb_set_mantissa_positive(n, 1);
        return 1;
    }
    size_t used = len - i;
    if (!nb_ensure_mbuf(n, used)) return 0;
    size_t off = n->m_len - used;
    memcpy(n->mantissa + off, bytes + i, used);
    n->m_used = used;
    nb_set_mantissa_positive(n, positive ? 1 : 0);
    return 1;
}

uint8_t *nb_export_mantissa_bytes(const nb_t *n, size_t *out_len) {
    if (!n) { if (out_len) *out_len = 0; return NULL; }
    if (n->m_used == 0) { if (out_len) *out_len = 0; return NULL; }
    uint8_t *r = (uint8_t*)malloc(n->m_used);
    if (!r) { if (out_len) *out_len = 0; return NULL; }
    memcpy(r, n->mantissa + (n->m_len - n->m_used), n->m_used);
    if (out_len) *out_len = n->m_used;
    return r;
}

int nb_set_exponent_bytes(nb_t *n, const uint8_t *bytes, size_t len, int positive) {
    if (!n) return 0;
    if (!bytes || len == 0) {
        if (n->exponent) { free(n->exponent); n->exponent = NULL; n->e_len = 0; }
        n->e_used = 0;
        nb_set_exponent_positive(n, 1);
        return 1;
    }
    size_t i = 0;
    while (i < len && bytes[i] == 0) i++;
    if (i == len) {
        if (n->exponent) { free(n->exponent); n->exponent = NULL; n->e_len = 0; }
        n->e_used = 0;
        nb_set_exponent_positive(n, 1);
        return 1;
    }
    size_t used = len - i;
    if (!nb_ensure_ebuf(n, used)) return 0;
    size_t off = n->e_len - used;
    memcpy(n->exponent + off, bytes + i, used);
    n->e_used = used;
    nb_set_exponent_positive(n, positive ? 1 : 0);
    return 1;
}

uint8_t *nb_export_exponent_bytes(const nb_t *n, size_t *out_len, int *out_positive) {
    if (!n) { if (out_len) *out_len = 0; if (out_positive) *out_positive = 1; return NULL; }
    if (n->e_used == 0) { if (out_len) *out_len = 0; if (out_positive) *out_positive = 1; return NULL; }
    uint8_t *r = (uint8_t*)malloc(n->e_used);
    if (!r) { if (out_len) *out_len = 0; if (out_positive) *out_positive = 1; return NULL; }
    memcpy(r, n->exponent + (n->e_len - n->e_used), n->e_used);
    if (out_len) *out_len = n->e_used;
    if (out_positive) *out_positive = nb_exponent_positive(n);
    return r;
}

/* compare exponent magnitude to uint64 value.
   return -1 if mag < v, 0 if equal, 1 if mag > v
*/
static int nb_exponent_mag_cmp_u64(const nb_t *n, uint64_t v) {
    if (!n) return (v == 0) ? 0 : -1;
    if (n->e_used == 0) {
        if (v == 0) return 0;
        return -1;
    }
    // if n->e_used > 8, it's definitely > v (unless v is huge, ggs)
    if (n->e_used > 8) return 1;
    // convert mag to u64
    uint64_t mag = 0;
    size_t off = n->e_len - n->e_used;
    for (size_t i = 0; i < n->e_used; ++i) {
        mag = (mag << 8) | n->exponent[off + i];
    }
    if (mag < v) return -1;
    if (mag > v) return 1;
    return 0;
}

/* add uint64 to exponent magnitude (in-place), expanding buffer as necessary.
   return 1 on success, 0 if out of memory
*/
static int nb_exponent_add_u64(nb_t *n, uint64_t v) {
    if (!n) return 0;
    if (v == 0) return 1;
    // if exponent zero, just set to v :3
    if (n->e_used == 0) {
        uint8_t tmp[8];
        for (int i = 7; i >= 0; --i) { tmp[i] = (uint8_t)(v & 0xFF); v >>= 8; }
        int idx = 0; while (idx < 8 && tmp[idx] == 0) idx++;
        return nb_set_exponent_bytes(n, tmp + idx, 8 - idx, 1);
    }
    // add from LSB
    // ensure there's room for possible carry
    if (!nb_ensure_ebuf(n, n->e_used + 1)) return 0;
    size_t off = n->e_len - n->e_used;
    ssize_t i = (ssize_t)(n->e_len - 1); // last byte index
    uint32_t carry = 0;
    // add low bytes of v into array
    while (v != 0 && i >= (ssize_t)off) {
        uint32_t sum = (uint32_t)n->exponent[i] + (uint32_t)(v & 0xFF) + carry;
        n->exponent[i] = (uint8_t)(sum & 0xFF);
        carry = sum >> 8;
        v >>= 8;
        --i;
    }
    // propagate carry if any or remaining v
    while ((v != 0 || carry) && i >= (ssize_t)off) {
        uint32_t sum = (uint32_t)n->exponent[i] + (uint32_t)(v & 0xFF) + carry;
        n->exponent[i] = (uint8_t)(sum & 0xFF);
        carry = sum >> 8;
        v >>= 8;
        --i;
    }
    // if still v or carry remains, insert bytes at front
    if (v != 0 || carry) {
        // gather remaining bytes into a small buffer (little-endian in addbuf)
        uint8_t addbuf[16];
        int addlen = 0;
        uint64_t rem = v;
        while (rem != 0) {
            addbuf[addlen++] = (uint8_t)(rem & 0xFF);
            rem >>= 8;
        }
        if (carry) addbuf[addlen++] = (uint8_t)carry;
        // reverse into big-endian in a tmp buffer and prepend to existing used bytes
        size_t old_used = n->e_used;
        size_t totalsz = (size_t)addlen + old_used;
        uint8_t *tmp = (uint8_t*)malloc(totalsz);
        if (!tmp) return 0;
        // write leading big-endian added bytes
        for (int j = 0; j < addlen; ++j) {
            tmp[j] = addbuf[addlen - 1 - j];
        }
        // copy existing used bytes (big-endian)
        if (old_used) {
            size_t old_off = n->e_len - old_used;
            memcpy(tmp + addlen, n->exponent + old_off, old_used);
        }
        // set exponent to the concatenation (nb_set_exponent_bytes will normalize)
        int rc = nb_set_exponent_bytes(n, tmp, totalsz, 1);
        free(tmp);
        return rc;
    }

    nb_normalize(n);
    return 1;
}

/* subtract uint64 from exponent magnitude in-place
   - if mag >= v: perform mag -= v and return 0 (no sign flip).
   - if mag < v: do NOT perform negative result; return 1 to indicate underflow
     (caller should flip sign and set mag = v - mag)
   return 0 on success (no underflow), 1 if underflow (mag < v), -1 if out of memory
*/
static int nb_exponent_sub_u64_inplace(nb_t *n, uint64_t v) {
    if (!n) return -1;
    if (v == 0) return 0;
    if (n->e_used == 0) {
        // 0 - v -> underflow (needs sign flip)
        return 1;
    }
    // if mag > 8 bytes, mag >= v for any v <= UINT64_MAX
    if (n->e_used > 8) {
        // perform subtraction at lsb side
        uint64_t borrow = 0;
        size_t off = n->e_len - n->e_used;
        ssize_t i = (ssize_t)(n->e_len - 1);
        uint64_t vv = v;
        while (i >= (ssize_t)off) {
            uint64_t sub = (uint64_t)n->exponent[i] - (vv & 0xFF) - borrow;
            n->exponent[i] = (uint8_t)(sub & 0xFF);
            borrow = (sub >> 63) & 1; // if sub underflowed, top bit set in two's complement; this extracts borrow
            vv >>= 8;
            --i;
        }
        if (borrow) { // shouldn't happen because mag > 8 bytes and v fits in 8 bytes
            return 1;
        }
        nb_normalize(n);
        return 0;
    }
    // mag fits in u64: read it
    uint64_t mag = 0;
    size_t off = n->e_len - n->e_used;
    for (size_t i = 0; i < n->e_used; ++i) mag = (mag << 8) | n->exponent[off + i];
    if (mag < v) return 1; // underflow
    uint64_t res = mag - v;
    // write back
    if (res == 0) {
        free(n->exponent);
        n->exponent = NULL;
        n->e_len = 0;
        n->e_used = 0;
    } else {
        uint8_t tmp[8];
        for (int i = 7; i >= 0; --i) { tmp[i] = (uint8_t)(res & 0xFF); res >>= 8; }
        int idx = 0; while (idx < 8 && tmp[idx] == 0) idx++;
        if (!nb_set_exponent_bytes(n, tmp + idx, 8 - idx, 1)) return -1;
    }
    return 0;
}

/* add signed 64-bit delta to exponent
   - if delta >= 0: effectively exponent = exponent + delta
   - if delta < 0: exponent = exponent - (-delta)
   supposed to handle exponent sign flips and expansion
   return 1 on success, 0 if out of memory
*/
int nb_exponent_add_signed(nb_t *n, int64_t delta) {
    if (!n) return 0;
    if (delta == 0) return 1;
    if (delta > 0) {
        // fprintf(stderr, "before add: e_used=%zu, delta=%lld\n", n->e_used, (long long)delta);
        // huh wtf

        uint64_t v = (uint64_t)delta;
        if (nb_exponent_positive(n)) {
            // +mag + v
            return nb_exponent_add_u64(n, v);
        } else {
            // exponent negative: mag_neg - v. If mag_neg > v => remain negative; else flip sign
            int cmp = nb_exponent_mag_cmp_u64(n, v);
            if (cmp >= 0) {
                // mag >= v => subtract
                int rc = nb_exponent_sub_u64_inplace(n, v);
                return (rc == 0);
            } else {
                // mag < v => new mag = v - mag ; sign becomes positive
                // compute mag as u64 if small
                uint64_t mag = 0;
                if (n->e_used == 0) mag = 0;
                else if (n->e_used <= 8) {
                    size_t off = n->e_len - n->e_used;
                    for (size_t i = 0; i < n->e_used; ++i) mag = (mag << 8) | n->exponent[off + i];
                } else {
                    // mag > v but we are in cmp < 0 which shouldn't occur
                    // fallback is uhh treat it like a success by setting exponent to (v) :3
                }
                uint64_t newmag = v - mag;
                // set exponent to newmag positive
                uint8_t tmp[8];
                for (int i = 7; i >= 0; --i) { tmp[i] = (uint8_t)(newmag & 0xFF); newmag >>= 8; }
                int idx = 0; while (idx < 8 && tmp[idx] == 0) idx++;
                if (!nb_set_exponent_bytes(n, tmp + idx, 8 - idx, 1)) return 0;
                nb_set_exponent_positive(n, 1);
                return 1;
            }
        }
    } else { // delta < 0
        uint64_t v = (uint64_t)(-delta);
        if (!nb_exponent_positive(n)) {
            // -mag - v => -(mag + v)
            if (!nb_exponent_add_u64(n, v)) return 0;
            // sign remains negative
            return 1;
        } else {
            // mag_pos - v => may remain positive or flip negative
            int cmp = nb_exponent_mag_cmp_u64(n, v);
            if (cmp > 0 || cmp == 0) {
                // mag >= v => subtract in-place
                int rc = nb_exponent_sub_u64_inplace(n, v);
                return (rc == 0);
            } else {
                // mag < v => newmag = v - mag ; sign flips negative
                uint64_t mag = 0;
                if (n->e_used == 0) mag = 0;
                else if (n->e_used <= 8) {
                    size_t off = n->e_len - n->e_used;
                    for (size_t i = 0; i < n->e_used; ++i) mag = (mag << 8) | n->exponent[off + i];
                }
                uint64_t newmag = v - mag;
                uint8_t tmp[8];
                for (int i = 7; i >= 0; --i) { tmp[i] = (uint8_t)(newmag & 0xFF); newmag >>= 8; }
                int idx = 0; while (idx < 8 && tmp[idx] == 0) idx++;
                if (!nb_set_exponent_bytes(n, tmp + idx, 8 - idx, 0)) return 0;
                nb_set_exponent_positive(n, 0);
                return 1;
            }
        }
    }
}

// hex parsing 🥀🥀🥀
static int hexval(char c) {
    if ('0' <= c && c <= '9') return c - '0';
    if ('a' <= c && c <= 'f') return c - 'a' + 10;
    if ('A' <= c && c <= 'F') return c - 'A' + 10;
    return -1;
}

int nb_set_mantissa_hex(nb_t *n, const char *hex, int positive) {
    if (!n || !hex) return 0;
    while (*hex && isspace((unsigned char)*hex)) ++hex;
    if (hex[0]=='0' && (hex[1]=='x' || hex[1]=='X')) hex += 2;
    size_t len = strlen(hex);
    size_t i = 0;
    while (i < len && hex[i] == '0') ++i;
    if (i == len) return nb_set_mantissa_bytes(n, NULL, 0, 1);
    size_t digits = len - i;
    size_t bytes = (digits + 1) / 2;
    uint8_t *buf = (uint8_t*)malloc(bytes);
    if (!buf) return 0;
    memset(buf, 0, bytes);
    size_t hi = i;
    size_t out = 0;
    if (digits % 2 == 1) {
        int v = hexval(hex[hi++]);
        if (v < 0) { free(buf); return 0; }
        buf[out++] = (uint8_t)v;
    }
    while (hi < len) {
        int a = hexval(hex[hi++]); int b = hexval(hex[hi++]);
        if (a<0||b<0) { free(buf); return 0; }
        buf[out++] = (uint8_t)((a<<4)|b);
    }
    int rc = nb_set_mantissa_bytes(n, buf, bytes, positive);
    free(buf);
    return rc;
}

int nb_set_exponent_hex(nb_t *n, const char *hex, int positive) {
    if (!n || !hex) return 0;
    while (*hex && isspace((unsigned char)*hex)) ++hex;
    if (hex[0]=='0' && (hex[1]=='x' || hex[1]=='X')) hex += 2;
    size_t len = strlen(hex);
    size_t i = 0;
    while (i < len && hex[i] == '0') ++i;
    if (i == len) return nb_set_exponent_bytes(n, NULL, 0, 1);
    size_t digits = len - i;
    size_t bytes = (digits + 1) / 2;
    uint8_t *buf = (uint8_t*)malloc(bytes);
    if (!buf) return 0;
    memset(buf, 0, bytes);
    size_t hi = i;
    size_t out = 0;
    if (digits % 2 == 1) {
        int v = hexval(hex[hi++]);
        if (v < 0) { free(buf); return 0; }
        buf[out++] = (uint8_t)v;
    }
    while (hi < len) {
        int a = hexval(hex[hi++]); int b = hexval(hex[hi++]);
        if (a<0||b<0) { free(buf); return 0; }
        buf[out++] = (uint8_t)((a<<4)|b);
    }
    int rc = nb_set_exponent_bytes(n, buf, bytes, positive);
    free(buf);
    return rc;
}

void nb_debug_print(const nb_t *n) {
    if (!n) { printf("nb: <null>\n"); return; }
    printf("numbat (nb_t) debug:\n");
    printf("  signs: 0x%02x  (mantissa %s, exponent %s)\n",
           n->signs, nb_mantissa_positive(n) ? "positive" : "negative", nb_exponent_positive(n) ? "positive" : "negative");
    printf("  mantissa used: %zu bytes\n", n->m_used);
    if (n->m_used) {
        printf("    mantissa (hex): ");
        size_t moff = n->m_len - n->m_used;
        for (size_t i = 0; i < n->m_used; ++i) printf("%02x", n->mantissa[moff + i]);
        printf("\n");
    } else {
        printf("    mantissa = 0\n");
    }
    printf("  exponent used: %zu bytes\n", n->e_used);
    if (n->e_used) {
        printf("    exponent (mag hex): ");
        size_t eoff = n->e_len - n->e_used;
        for (size_t i = 0; i < n->e_used; ++i) printf("%02x", n->exponent[eoff + i]);
        printf("\n");
    } else {
        printf("    exponent = 0\n");
    }
}

#ifdef NB_TEST
int main(void) {
    nb_t *n = nb_new();
    puts("=== set mantissa to 0x01 (positive) and exponent to 0x0001 (positive) ===");
    uint8_t m1[] = { 0x01 };
    nb_set_mantissa_bytes(n, m1, 1, 1);
    uint8_t e1[] = { 0x01 };
    nb_set_exponent_bytes(n, e1, 1, 1);
    nb_debug_print(n);

    puts("\n=== add +255 to exponent (+255) => exponent should expand ===");
    if (!nb_exponent_add_signed(n, 255)) { printf("OOM or error\n"); return 1; }
    nb_debug_print(n);

    puts("\n=== add +0x123456789abcdef0 (big) by using multiple adds (simulate) ===");
    // 繰り返しチャンクを使用して大きな数字を追加してみましょう
    if (!nb_exponent_add_signed(n, 0x7fffffff)) { puts("fail"); }
    if (!nb_exponent_add_signed(n, 0x7fffffff)) { puts("fail"); }
    nb_debug_print(n);

    puts("\n=== subtract large value to cause sign flip ===");
    // set exponent to small positive 5
    nb_set_exponent_hex(n, "05", 1);
    nb_debug_print(n);
    // subtract 10 => should flip negative and exponent magnitude becomes 5
    nb_exponent_add_signed(n, -10);
    nb_debug_print(n);

    puts("\n=== mantissa zero behavior ===");
    nb_set_mantissa_bytes(n, NULL, 0, 1);
    nb_debug_print(n);

    nb_free(n);
    return 0;
}
#endif
