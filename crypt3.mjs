
import { m_sbox, ip_maskl, ip_maskr, fp_maskl, fp_maskr, key_perm_maskl, key_perm_maskr, comp_maskl, comp_maskr, psbox } from "./alg-des-tables.mjs"


const ALG_SPECIFIC_SIZE = 8192;
const CRYPT_OUTPUT_SIZE = 384;
const CRYPT_MAX_PASSPHRASE_SIZE = 512;
const CRYPT_GENSALT_OUTPUT_SIZE = 192;
const DES_TRD_OUTPUT_LEN = 14;                /* SShhhhhhhhhhh0 */

const CRYPT_DATA_RESERVED_SIZE = 767;
const CRYPT_DATA_INTERNAL_SIZE = 30720;
const ascii64 = "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz\x00";

const key_shifts =
    [
        1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1
    ];

class DesCtx {
    constructor() {
        this.keysl = new Array(16).fill(0); // Array of 16 elements, initialized to 0
        this.keysr = new Array(16).fill(0); // Array of 16 elements, initialized to 0
        this.saltbits = 0;
    }
}

class DesBuffer {
    constructor() {
        this.ctx = new DesCtx();            // DesCtx object
        this.keybuf = new Uint8Array(8);    // Byte array of 8 elements
        this.pkbuf = new Uint8Array(8);     // Byte array of 8 elements
    }
}

class CryptInternal {
    constructor() {
        this.alg_specific = new DesBuffer();
    }
}

class CryptData {
    constructor() {
        this.output = new Array(CRYPT_OUTPUT_SIZE).fill('\0');
        this.setting = new Array(CRYPT_OUTPUT_SIZE).fill('\0');
        this.input = new Array(CRYPT_MAX_PASSPHRASE_SIZE).fill('\0');
        this.reserved = new Array(CRYPT_DATA_RESERVED_SIZE).fill('\0');
        this.initialized = '\0';
        this.internal = new CryptInternal();
    }
}

class HashFn {
    constructor(prefix, plen, crypt, gensalt, nrbytes, is_strong) {
        this.prefix = prefix;
        this.plen = plen;
        this.crypt = crypt;
        this.gensalt = gensalt;
        this.nrbytes = nrbytes;
        this.is_strong = is_strong;
    }
}

const hash_algorithms = [
    new HashFn("", 0, cryptDescryptRn, gensaltDescryptRn, 2, 0)
]


function asciiToBin(ch) {
    if (ch > 'z') {
        return -1;
    }
    if (ch >= 'a') {
        return ch.charCodeAt(0) - 'a'.charCodeAt(0) + 38;
    }
    if (ch > 'Z') {
        return -1;
    }
    if (ch >= 'A') {
        return ch.charCodeAt(0) - 'A'.charCodeAt(0) + 12;
    }
    if (ch > '9') {
        return -1;
    }
    if (ch >= '.') {
        return ch.charCodeAt(0) - '.'.charCodeAt(0);
    }
    return -1;
}

function be32ToCpu(buf) {
    return ((buf[0] << 24) >>> 0) |  // Use unsigned right shift to ensure a 32-bit unsigned result
        (buf[1] << 16) |
        (buf[2] << 8) |
        (buf[3]);
}

function cpuToBe32(buf, n, start = 0) {
    buf[start] = (n >>> 24) & 0xFF; // Right shift and mask to get the most significant byte
    buf[start + 1] = (n >>> 16) & 0xFF; // Next byte
    buf[start + 2] = (n >>> 8) & 0xFF;  // Next byte
    buf[start + 3] = n & 0xFF;          // Least significant byte
}

function isDesSaltChar(c) {
    return ((c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') ||
        c === '.' || c === '/');
}

function strcspn(str, chars) {
    const regex = new RegExp(`[^${chars}]`);
    const index = str.search(regex);
    return index === -1 ? str.length : index;
}

function checkBadSaltChars(setting) {
    return ! /^[a-zA-Z0-9]+$/.test(setting);
}

function getInternal(data) {
    data.internal = new CryptInternal();
    return data.internal;
}

function getHashFn(setting) {
    for (const h of hash_algorithms) {
        if (setting === '' ||
            (isDesSaltChar(setting[0]) && isDesSaltChar(setting[1]))) {
            return h;
        }
    }
    return null; // Return null to indicate no match found
}

function desSetKey(ctx, key) {
    let rawkey0, rawkey1, k0, k1, t0, t1;
    let shifts = 0;

    rawkey0 = be32ToCpu(key.slice(0, 4));
    rawkey1 = be32ToCpu(key.slice(4, 8));

    // Do key permutation and split into two 28-bit subkeys.
    k0 = key_perm_maskl[0][(rawkey0 >>> 25) & 0x7f]
        | key_perm_maskl[1][(rawkey0 >>> 17) & 0x7f]
        | key_perm_maskl[2][(rawkey0 >>> 9) & 0x7f]
        | key_perm_maskl[3][(rawkey0 >>> 1) & 0x7f]
        | key_perm_maskl[4][(rawkey1 >>> 25) & 0x7f]
        | key_perm_maskl[5][(rawkey1 >>> 17) & 0x7f]
        | key_perm_maskl[6][(rawkey1 >>> 9) & 0x7f]
        | key_perm_maskl[7][(rawkey1 >>> 1) & 0x7f];
    k1 = key_perm_maskr[0][(rawkey0 >>> 25) & 0x7f]
        | key_perm_maskr[1][(rawkey0 >>> 17) & 0x7f]
        | key_perm_maskr[2][(rawkey0 >>> 9) & 0x7f]
        | key_perm_maskr[3][(rawkey0 >>> 1) & 0x7f]
        | key_perm_maskr[4][(rawkey1 >>> 25) & 0x7f]
        | key_perm_maskr[5][(rawkey1 >>> 17) & 0x7f]
        | key_perm_maskr[6][(rawkey1 >>> 9) & 0x7f]
        | key_perm_maskr[7][(rawkey1 >>> 1) & 0x7f];

    // Rotate subkeys and do compression permutation.
    for (let round = 0; round < 16; round++) {
        shifts += key_shifts[round];

        t0 = ((k0 << shifts) | (k0 >>> (28 - shifts))) & 0xfffffff; // 28-bit rotation
        t1 = ((k1 << shifts) | (k1 >>> (28 - shifts))) & 0xfffffff; // 28-bit rotation

        ctx.keysl[round] =
            comp_maskl[0][(t0 >>> 21) & 0x7f]
            | comp_maskl[1][(t0 >>> 14) & 0x7f]
            | comp_maskl[2][(t0 >>> 7) & 0x7f]
            | comp_maskl[3][t0 & 0x7f]
            | comp_maskl[4][(t1 >>> 21) & 0x7f]
            | comp_maskl[5][(t1 >>> 14) & 0x7f]
            | comp_maskl[6][(t1 >>> 7) & 0x7f]
            | comp_maskl[7][t1 & 0x7f];

        ctx.keysr[round] =
            comp_maskr[0][(t0 >>> 21) & 0x7f]
            | comp_maskr[1][(t0 >>> 14) & 0x7f]
            | comp_maskr[2][(t0 >>> 7) & 0x7f]
            | comp_maskr[3][t0 & 0x7f]
            | comp_maskr[4][(t1 >>> 21) & 0x7f]
            | comp_maskr[5][(t1 >>> 14) & 0x7f]
            | comp_maskr[6][(t1 >>> 7) & 0x7f]
            | comp_maskr[7][t1 & 0x7f];
    }
}

function desCryptBlock(ctx, out, input, count, decrypt) {
    let l_in, r_in, l_out, r_out;
    let l, r, kl1, kr1;
    let f, r48l, r48r;
    let saltbits = ctx.saltbits;
    let round;

    // Default to 1 if count is zero
    count = count || 1;

    if (decrypt) {
        kl1 = ctx.keysl.slice().reverse();
        kr1 = ctx.keysr.slice().reverse();
    } else {
        kl1 = ctx.keysl.slice();
        kr1 = ctx.keysr.slice();
    }

    // Read the input
    l_in = be32ToCpu(input.slice(0, 4));
    r_in = be32ToCpu(input.slice(4, 8));

    // Do initial permutation
    l = ip_maskl[0][(l_in >>> 24) & 0xff]
        | ip_maskl[1][(l_in >>> 16) & 0xff]
        | ip_maskl[2][(l_in >>> 8) & 0xff]
        | ip_maskl[3][l_in & 0xff]
        | ip_maskl[4][(r_in >>> 24) & 0xff]
        | ip_maskl[5][(r_in >>> 16) & 0xff]
        | ip_maskl[6][(r_in >>> 8) & 0xff]
        | ip_maskl[7][r_in & 0xff];
    r = ip_maskr[0][(l_in >>> 24) & 0xff]
        | ip_maskr[1][(l_in >>> 16) & 0xff]
        | ip_maskr[2][(l_in >>> 8) & 0xff]
        | ip_maskr[3][l_in & 0xff]
        | ip_maskr[4][(r_in >>> 24) & 0xff]
        | ip_maskr[5][(r_in >>> 16) & 0xff]
        | ip_maskr[6][(r_in >>> 8) & 0xff]
        | ip_maskr[7][r_in & 0xff];

    do {
        round = 16;
        do {
            // Expand R to 48 bits
            r48l = ((r & 0x00000001) << 23)
                | ((r & 0xf8000000) >>> 9)
                | ((r & 0x1f800000) >>> 11)
                | ((r & 0x01f80000) >>> 13)
                | ((r & 0x001f8000) >>> 15);

            r48r = ((r & 0x0001f800) << 7)
                | ((r & 0x00001f80) << 5)
                | ((r & 0x000001f8) << 3)
                | ((r & 0x0000001f) << 1)
                | ((r & 0x80000000) >>> 31);

            // Apply salt and permuted round key
            f = (r48l ^ r48r) & saltbits;
            r48l ^= f ^ kl1[16 - round];
            r48r ^= f ^ kr1[16 - round];

            // Do sbox lookups and the pbox permutation at the same time
            f = psbox[0][m_sbox[0][r48l >>> 12]]
                | psbox[1][m_sbox[1][r48l & 0xfff]]
                | psbox[2][m_sbox[2][r48r >>> 12]]
                | psbox[3][m_sbox[3][r48r & 0xfff]];

            // Complete f()
            f ^= l;
            l = r;
            r = f;

        } while (--round);

        r = l;
        l = f;

    } while (--count);

    /* Do final permutation (inverse of IP).  */
    l_out =
        fp_maskl[0][(l >>> 24) & 0xff]
        | fp_maskl[1][(l >>> 16) & 0xff]
        | fp_maskl[2][(l >>> 8) & 0xff]
        | fp_maskl[3][(l >>> 0) & 0xff]
        | fp_maskl[4][(r >>> 24) & 0xff]
        | fp_maskl[5][(r >>> 16) & 0xff]
        | fp_maskl[6][(r >>> 8) & 0xff]
        | fp_maskl[7][(r >>> 0) & 0xff];
    r_out =
        fp_maskr[0][(l >>> 24) & 0xff]
        | fp_maskr[1][(l >>> 16) & 0xff]
        | fp_maskr[2][(l >>> 8) & 0xff]
        | fp_maskr[3][(l >>> 0) & 0xff]
        | fp_maskr[4][(r >>> 24) & 0xff]
        | fp_maskr[5][(r >>> 16) & 0xff]
        | fp_maskr[6][(r >>> 8) & 0xff]
        | fp_maskr[7][(r >>> 0) & 0xff];

    // Write the output
    cpuToBe32(out, l_out);
    cpuToBe32(out, r_out, 4);
}

function desSetSalt(ctx, salt) {
    let obit, saltbit, saltbits;
    saltbits = 0;
    saltbit = 1;
    obit = 0x800000;

    for (let i = 0; i < 24; i++) {
        if (salt & saltbit) {
            saltbits |= obit;
        }
        saltbit <<= 1;
        obit >>>= 1; // Use unsigned right shift in JavaScript
    }

    ctx.saltbits = saltbits;
}

function gensaltDescryptRn(count, rbytes, nrbytes, output, outputSize) {
    if (outputSize < 3) {
        throw new Error("Output size too small");
    }

    if (nrbytes < 2 || count !== 0) {
        throw new Error("Invalid input");
    }

    output[0] = ascii64[rbytes[0] & 0x3f];
    output[1] = ascii64[rbytes[1] & 0x3f];
    output[2] = '\0';
}

function desGenHash(ctx, count, output, cbuf) {
    let plaintext = new Uint8Array(8); // Initialized to 0
    desCryptBlock(ctx, cbuf, plaintext, count, false);

    // Encoding the result
    let sptr = 0; // Use an index instead of a pointer
    const end = 8;
    let c1, c2;

    while (sptr < end) {
        c1 = cbuf[sptr++];
        output.push(ascii64[c1 >> 2]);
        c1 = (c1 & 0x03) << 4;

        if (sptr >= end) {
            output.push(ascii64[c1]);
            break;
        }

        c2 = cbuf[sptr++];
        c1 |= c2 >> 4;
        output.push(ascii64[c1]);
        c1 = (c2 & 0x0f) << 2;

        if (sptr >= end) {
            output.push(ascii64[c1]);
            break;
        }

        c2 = cbuf[sptr++];
        c1 |= c2 >> 6;
        output.push(ascii64[c1]);
        output.push(ascii64[c2 & 0x3f]);
    }
}

function cryptDescryptRn(phrase, setting, output, scratch) {
    if (output.length < DES_TRD_OUTPUT_LEN) {
        throw new Error("Output or scratch size too small");
    }

    let ctx = scratch.ctx; // Assuming `scratch` is an object with a `ctx` property
    let salt = 0;
    let cp = []; // Assuming output is to be collected in an array

    // Processing the salt from the setting
    let i = asciiToBin(setting[0]);
    if (i < 0) {
        throw new Error("Invalid setting character");
    }
    salt = i;
    i = asciiToBin(setting[1]);
    if (i < 0) {
        throw new Error("Invalid setting character");
    }
    salt |= (i << 6);

    // Write the canonical form of the salt to cp
    cp.push(ascii64[salt & 0x3f]);
    cp.push(ascii64[(salt >> 6) & 0x3f]);

    // Copy the first 8 characters of the phrase into keybuf
    for (i = 0; i < 8; i++) {
        scratch.keybuf[i] = phrase[i] ? phrase.charCodeAt(i) << 1 : 0;
    }

    desSetKey(ctx, scratch.keybuf);
    desSetSalt(ctx, salt);
    desGenHash(ctx, 25, cp, scratch.pkbuf);
    output = cp.join('')
    return output;
}


export function crypt(phrase, setting, data = new CryptData()) {
    if (!phrase || !setting) {
        throw new Error("bad phrase or setting");
    }
    /* Do these strlen() calls before reading prefixes of either
       'phrase' or 'setting', so we get a predictable crash if they are
       not valid strings.  */
    if (phrase.length >= CRYPT_MAX_PASSPHRASE_SIZE) {
        throw new Error("phrase too long");
    }
    if (checkBadSaltChars(setting)) {
       throw new Error("bad salt");
    }

    let h = getHashFn(setting);
    if (!h) {
        throw new Error("no hash function")
    }
    const cint = getInternal(data);
    return h.crypt(phrase, setting, data.output, cint.alg_specific);
}
