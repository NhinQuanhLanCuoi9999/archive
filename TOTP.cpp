#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
#include <math.h>

#define SHA1_BLOCK_SIZE 64
#define SHA1_HASH_SIZE 20

// ---------------------- BASE32 ---------------------- //
int base32_char_to_val(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= '2' && c <= '7') return c - '2' + 26;
    return -1;
}

int base32_decode(const char *input, uint8_t *output) {
    int buffer = 0, bitsLeft = 0, count = 0;
    for (int i = 0; input[i]; i++) {
        int val = base32_char_to_val(input[i]);
        if (val < 0) continue;

        buffer <<= 5;
        buffer |= val;
        bitsLeft += 5;

        if (bitsLeft >= 8) {
            output[count++] = (buffer >> (bitsLeft - 8)) & 0xFF;
            bitsLeft -= 8;
        }
    }
    return count;
}

// ---------------------- SHA1 ---------------------- //
uint32_t rol(uint32_t value, uint32_t bits) {
    return ((value << bits) | (value >> (32 - bits)));
}

void sha1(const uint8_t *data, size_t len, uint8_t hash[SHA1_HASH_SIZE]) {
    uint32_t h0 = 0x67452301;
    uint32_t h1 = 0xEFCDAB89;
    uint32_t h2 = 0x98BADCFE;
    uint32_t h3 = 0x10325476;
    uint32_t h4 = 0xC3D2E1F0;

    size_t new_len = len + 1;
    while ((new_len % 64) != 56) new_len++;

    uint8_t *msg = (uint8_t *)calloc(new_len + 8, 1);
    memcpy(msg, data, len);
    msg[len] = 0x80;

    uint64_t bits_len = len * 8;
    for (int i = 0; i < 8; i++) {
        msg[new_len + i] = (bits_len >> ((7 - i) * 8)) & 0xFF;
    }

    for (size_t offset = 0; offset < new_len; offset += 64) {
        uint32_t w[80];
        for (int i = 0; i < 16; i++) {
            w[i] = (msg[offset + i * 4] << 24) |
                   (msg[offset + i * 4 + 1] << 16) |
                   (msg[offset + i * 4 + 2] << 8) |
                   (msg[offset + i * 4 + 3]);
        }
        for (int i = 16; i < 80; i++) {
            w[i] = rol(w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16], 1);
        }

        uint32_t a = h0, b = h1, c = h2, d = h3, e = h4;
        for (int i = 0; i < 80; i++) {
            uint32_t f, k;
            if (i < 20) {
                f = (b & c) | ((~b) & d); k = 0x5A827999;
            } else if (i < 40) {
                f = b ^ c ^ d; k = 0x6ED9EBA1;
            } else if (i < 60) {
                f = (b & c) | (b & d) | (c & d); k = 0x8F1BBCDC;
            } else {
                f = b ^ c ^ d; k = 0xCA62C1D6;
            }

            uint32_t temp = rol(a,5) + f + e + k + w[i];
            e = d; d = c; c = rol(b,30); b = a; a = temp;
        }

        h0 += a; h1 += b; h2 += c; h3 += d; h4 += e;
    }

    free(msg);
    uint32_t temp[5] = { h0, h1, h2, h3, h4 };
    for (int i = 0; i < 5; i++) {
        hash[i*4+0] = (temp[i] >> 24) & 0xFF;
        hash[i*4+1] = (temp[i] >> 16) & 0xFF;
        hash[i*4+2] = (temp[i] >> 8) & 0xFF;
        hash[i*4+3] = (temp[i]) & 0xFF;
    }
}

// ---------------------- HMAC-SHA1 ---------------------- //
void hmac_sha1(const uint8_t *key, size_t key_len,
               const uint8_t *msg, size_t msg_len,
               uint8_t hmac[SHA1_HASH_SIZE]) {
    uint8_t ipad[SHA1_BLOCK_SIZE], opad[SHA1_BLOCK_SIZE];
    uint8_t key_block[SHA1_BLOCK_SIZE] = {0};

    if (key_len > SHA1_BLOCK_SIZE) {
        sha1(key, key_len, key_block);
    } else {
        memcpy(key_block, key, key_len);
    }

    for (int i = 0; i < SHA1_BLOCK_SIZE; i++) {
        ipad[i] = key_block[i] ^ 0x36;
        opad[i] = key_block[i] ^ 0x5C;
    }

    uint8_t inner_hash_input[SHA1_BLOCK_SIZE + msg_len];
    memcpy(inner_hash_input, ipad, SHA1_BLOCK_SIZE);
    memcpy(inner_hash_input + SHA1_BLOCK_SIZE, msg, msg_len);

    uint8_t inner_hash[SHA1_HASH_SIZE];
    sha1(inner_hash_input, SHA1_BLOCK_SIZE + msg_len, inner_hash);

    uint8_t outer_hash_input[SHA1_BLOCK_SIZE + SHA1_HASH_SIZE];
    memcpy(outer_hash_input, opad, SHA1_BLOCK_SIZE);
    memcpy(outer_hash_input + SHA1_BLOCK_SIZE, inner_hash, SHA1_HASH_SIZE);

    sha1(outer_hash_input, SHA1_BLOCK_SIZE + SHA1_HASH_SIZE, hmac);
}

// ---------------------- TOTP ---------------------- //
uint32_t generate_totp(const uint8_t *key, int key_len, uint64_t timestamp) {
    uint64_t counter = timestamp / 30;
    uint8_t msg[8];
    for (int i = 7; i >= 0; i--) {
        msg[i] = counter & 0xFF;
        counter >>= 8;
    }

    uint8_t hash[SHA1_HASH_SIZE];
    hmac_sha1(key, key_len, msg, 8, hash);

    int offset = hash[19] & 0x0F;
    uint32_t bin_code = ((hash[offset] & 0x7F) << 24) |
                        ((hash[offset+1] & 0xFF) << 16) |
                        ((hash[offset+2] & 0xFF) << 8) |
                        (hash[offset+3] & 0xFF);

    return bin_code % 1000000;
}

// ---------------------- MAIN ---------------------- //
int main() {
    char base32[100];
    system("chcp 65001 >> out");
    printf("Nhập mã Base32 secret: ");
    scanf("%s", base32);

    uint8_t key[64];
    int key_len = base32_decode(base32, key);

    while (1) {
        time_t now = time(NULL);
        uint32_t code = generate_totp(key, key_len, now);
        printf("\r🔐 Mã TOTP: %06d | Reset sau %2ld giây  ", code, 30 - (now % 30));
        fflush(stdout);
        sleep(1);
    }
    return 0;
}
