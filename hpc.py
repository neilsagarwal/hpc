# hpc.py
# author: Neil Agarwal <neilagarwal@berkeley.edu>

# =============================================================================
# Python Implementation of the Hasty Pudding Cipher
# =============================================================================

import math
from enum import Enum

# Internal "random" numbers
IRN1 = 3141592653589793238    # PI19
IRN2 = 2718281828459045235    # E19
IRN3 = 14142135623730950488   # R220

# Perma array for tiny subcipher
Perma = [
    0x243F6A8885A308D3 ^ 0,   0x13198A2E03707344 ^ 1,
    0xA4093822299F31D0 ^ 2,   0x082EFA98EC4E6C89 ^ 3,
    0x452821E638D01377 ^ 4,   0xBE5466CF34E90C6C ^ 5,
    0xC0AC29B7C97C50DD ^ 6,   0x9216D5D98979FB1B ^ 7,
    0xB8E1AFED6A267E96 ^ 8,   0xA458FEA3F4933D7E ^ 9,
    0x0D95748F728EB658 ^ 10,  0x7B54A41DC25A59B5 ^ 11,
    0xCA417918B8DB38EF ^ 12,  0xB3EE1411636FBC2A ^ 13,
    0x61D809CCFB21A991 ^ 14,  0x487CAC605DEC8032 ^ 15
]

Permai = [
   0xA4093822299F31D0 ^ 2,   0x61D809CCFB21A991 ^ 14,
   0x487CAC605DEC8032 ^ 15,  0x243F6A8885A308D3 ^ 0,
   0x13198A2E03707344 ^ 1,   0x7B54A41DC25A59B5 ^ 11,
   0xB8E1AFED6A267E96 ^ 8,   0x452821E638D01377 ^ 4,
   0x0D95748F728EB658 ^ 10,  0x082EFA98EC4E6C89 ^ 3,
   0xB3EE1411636FBC2A ^ 13,  0x9216D5D98979FB1B ^ 7,
   0xBE5466CF34E90C6C ^ 5,   0xC0AC29B7C97C50DD ^ 6,
   0xA458FEA3F4933D7E ^ 9,   0xCA417918B8DB38EF ^ 12
 ]

Permb = [
   0xB7E151628AED2A6A -0,   0xBF7158809CF4F3C7 -1,
   0x62E7160F38B4DA56 -2,   0xA784D9045190CFEF -3,
   0x324E7738926CFBE5 -4,   0xF4BF8D8D8C31D763 -5,
   0xDA06C80ABB1185EB -6,   0x4F7C7B5757F59584 -7,
   0x90CFD47D7C19BB42 -8,   0x158D9554F7B46BCE -9,
   0x8A9A276BCFBFA1C8 -10,  0xE5AB6ADD835FD1A0 -11,
   0x86D1BF275B9B241D -12,  0xF0D3D37BE67008E1 -13,
   0x0FF8EC6D31BEB5CC -14,  0xEB64749A47DFDFB9 -15
]

Permbi = [
   0xE5AB6ADD835FD1A0 -11,  0xF0D3D37BE67008E1 -13,
   0x90CFD47D7C19BB42 -8,   0xF4BF8D8D8C31D763 -5,
   0x4F7C7B5757F59584 -7,   0x324E7738926CFBE5 -4,
   0x62E7160F38B4DA56 -2,   0xBF7158809CF4F3C7 -1,
   0x8A9A276BCFBFA1C8 -10,  0xEB64749A47DFDFB9 -15,
   0xB7E151628AED2A6A -0,   0xDA06C80ABB1185EB -6,
   0x0FF8EC6D31BEB5CC -14,  0x86D1BF275B9B241D -12,
   0x158D9554F7B46BCE -9,   0xA784D9045190CFEF -3
]

# number of passes in stirring function
NUM_STIR_PASSES = 3

BACKUP = 0
BACKUPSUBCIPHER = [0] * (1+5)

# helper functions to ensure everything is % 64
def mod(x): return x & 0xFFFFFFFFFFFFFFFF
def m_xor(x, y): return mod(x ^ y)
def m_lsh(x, y): return mod(x << y)
def m_rsh(x, y): return mod(x >> y)
def m_add(x, y): return mod(x + y)
def m_sub(x, y): return mod(x - y)
def m_mul(x, y): return mod(x * y)
def m_or(x, y): return mod(x | y)
def m_and(x, y): return mod(x & y)

# masking helper function
def mask_lower(n, size):
  mask = (1 << size) - 1
  return mod(n) & mask

# rotate x shift left/right bits
def m_lrot(x, shift, size=64):
    return mask_lower(m_or(m_lsh(x, shift), m_rsh(x, size - shift)), size)
def m_rrot(x, shift, size=64):
    return mask_lower(m_or(m_lsh(x, size - shift), m_rsh(x, shift)), size)

def create_kx_table(key, sub_cipher_num, key_len):
    """
    Pseduorandomly derived by the key, the Key Expansion Table contains
    286 words of 64-bits. This table is "firewalled": knowing a KX table won't
    help find the original key, or a KX table for a different subcipher.

    Args:
        key: the secret key (atleast 0 bits)
        sub_cipher_num: the sub-cipher number (from 1 to 5, 1 is HPC-Tiny)
        key_len: length of key in bits
    Returns:
        key expansion table of length 286
        :type key: list

    """

    assert(1 <= sub_cipher_num <= 5)

    if (type(key) != str): key = hex(key)

    kx = [] # initialization of key expansion table

    # Initial set up of the key expansion of the table
    kx.append(m_add(IRN1, sub_cipher_num))
    kx.append(m_mul(IRN2, key_len))

    # left rotation
    kx.append(m_lrot(IRN3, sub_cipher_num))

    for i in range(3, 256):
        kx.append(m_add(m_xor(m_xor(m_rsh(kx[i-3], 23),
            m_lsh(kx[i-3], 41)), kx[i-2]),kx[i-1]))

    # Clean up the key before incorporating
    cleaned_key = hex_str_to_arr(key)

    # Incorporating the content of the key into key expansion table
    for j in range(math.ceil(len(cleaned_key)/128)):
        for i in range(min(len(cleaned_key)-128*j, 128)):
            kx[i] = m_xor(kx[i], cleaned_key[i+j*128])
        stir(kx)

    # finish up key expansion
    for i in range(30):
        kx.append(kx[i])
    return kx

def hex_str_to_arr(txt, required_len=None):
    """
    Convert hex string into an array of 64-bit words

    Args:
        txt: a hex string (atleast 0 bits)
    Returns:
        arr: input as list of 64-bit words

    """
    assert(txt[:2] == "0x")
    txt = txt[2:]
    if required_len:
        assert(len(txt) == required_len)
    arr = []
    for i in range(len(txt)//16):
        arr.append(int("0x" + txt[i*16:(i+1)*16], 16))
    if (len(txt) % 16 != 0):
        arr.append(int("0x" + txt[(len(txt)//16)*16:], 16))

    return arr

def short_encrypt(s, kx, spice, blocksize, backup, lmask=None):
    """ Encryption of Tiny Subciphers (37 <= blocksize < 65) """

    if not lmask: lmask = (1 << 64) - 1

    s0 = s[0]

    for cycle_num in range(1 + backup):
        s0 = m_add(m_add(s0, kx[blocksize]) & lmask, cycle_num) & lmask
        LBH = (blocksize+1)//2
        LBQ = (LBH+1)//2
        LBT = (blocksize+LBQ)//4 + 2
        GAP = 64 - blocksize
        for i in range(8):
            k = kx[s0&255] + spice[i]
            s0 = m_add(s0, k<<8) & lmask
            s0 = m_xor(s0, (k>>GAP) & (~255)) & lmask
            s0 = m_add(s0, s0<<(LBH+i)) & lmask
            t = spice[i^7]
            s0 = m_xor(s0, t) & lmask
            s0 = m_sub(s0, t>>(GAP+i)) & lmask
            s0 = m_add(s0, t>>13) & lmask
            s0 = m_xor(s0, s0>>LBH) & lmask
            t = s0&255
            k = kx[t]
            k ^= spice[i^4]
            k = mod(kx[t+3*i+1] + (k>>23) + (k<<41))
            s0 = m_xor(s0, k<<8) & lmask
            s0 = m_sub(s0, (k>>GAP) & (~255)) & lmask
            s0 = m_sub(s0, s0<<LBH) & lmask
            t = spice[i^1] ^ (IRN1+blocksize)
            s0 = m_add(s0, t<<3) & lmask
            s0 = m_xor(s0, t>>(GAP+2)) & lmask
            s0 = m_sub(s0, t) & lmask
            s0 = m_xor(s0, s0>>LBQ) & lmask
            s0 = m_add(s0, Permb[s0&15]) & lmask
            t = spice[i^2]
            s0 = m_xor(s0, t>>(GAP+4)) & lmask
            s0 = m_add(s0, s0<<(LBT + (s0&15))) & lmask
            s0 = m_add(s0, t) & lmask
            s0 = m_xor(s0, s0>>LBH) & lmask

        s0 = mask_lower(m_add(s0, kx[blocksize+8]),  blocksize)
    return [s0]

def short_decrypt(s, kx, spice, blocksize, backup, lmask=None):
    """ Decryption of Tiny Subciphers (37 <= blocksize < 65) """

    if not lmask: lmask = (1 << 64) - 1

    LBH = (blocksize+1)//2
    LBQ = (LBH+1)//2
    LBT = (blocksize+LBQ)//4 + 2
    GAP = 64 - blocksize

    s0 = s[0]

    for cycle_num in reversed(range(1 + backup)):

        s0 = m_sub(s0, kx[blocksize+8]) & lmask

        for i in reversed(range(8)):
            t = spice[i^2]
            s0 = m_xor(s0, s0>>LBH) & lmask
            s0 = m_sub(s0, t) & lmask
            s0 = m_sub(s0, (s0 - (s0<<(LBT + (s0&15)))) << (LBT + (s0&15)))
            s0 = m_xor(s0, t>>(GAP+4)) & lmask
            s0 = m_sub(s0, Permbi[s0&15]) & lmask
            t = spice[i^1] ^ (IRN1+blocksize)
            s0 ^= s0>>LBQ; s0 ^= s0>>(2*LBQ)
            s0 = m_add(s0, t) & lmask
            s0 = m_xor(s0, t>>(GAP+2)) & lmask
            s0 = m_sub(s0, t<<3) & lmask
            s0 = m_add(s0, s0<<LBH) & lmask
            t = s0&255
            k = kx[t]
            k ^= spice[i^4]
            k = mod(kx[t+3*i+1] + (k>>23) + (k<<41))
            s0 = m_add(s0, (k>>GAP) & (~255)) & lmask
            s0 = m_xor(s0, k<<8) & lmask
            s0 = m_xor(s0, s0>>LBH) & lmask
            t = spice[i^7]
            s0 = m_sub(s0, t>>13) & lmask
            s0 = m_add(s0, t>>(GAP+i)) & lmask
            s0 = m_xor(s0, t) & lmask
            s0 = m_sub(s0, s0<<(LBH+i)) & lmask
            k = kx[s0&255] + spice[i]
            s0 = m_xor(s0, (k>>GAP) & (~255)) & lmask
            s0 = m_sub(s0, k<<8) & lmask

        s0 = mask_lower(m_sub(m_sub(s0, cycle_num), kx[blocksize]),  blocksize)

    return [s0]

def tiny_encrypt(ptxt, kx, spice, blocksize, backup):
    """ Encryption of Tiny Subciphers (0 <= blocksize < 36) """

    s0 = ptxt[0]
    for cycle_num in range(1 + backup):
        s0 = mask_lower(m_add(s0, cycle_num), blocksize)
        s0 = m_add(s0, kx[blocksize])
        if 1 <= blocksize < 7:
            s0 = tiny_1_6_encrypt(s0, kx, spice, blocksize, cycle_num)
        else:
            temp = []
            for i in range(8):
                temp.append(m_xor(spice[i], kx[4 * blocksize + 16 + i]))
            spice_long = [0, 0, 0, 0, 0, 0, 0, 0]
            temp[0] = m_add(temp[0], cycle_num)
            temp = long_encrypt(temp, kx, spice_long, 512, 0)
            temp.append(temp[7])
            temp.append(temp[7])

            for i in range(8):
                t0 = m_add(m_lsh(temp[8], 21), m_rsh(temp[8], 13))
                temp[8] = m_add(temp[8], m_xor(t0, m_add(temp[i], kx[16+i])))
                temp[9] = m_xor(temp[8], temp[9])

            if (7 <= blocksize <= 15):
                s0 = tiny_7_15_encrypt(s0, temp, kx, blocksize)
            else:
                s0 = tiny_16_35_encrypt(s0, temp, kx, blocksize)

        s0 = mask_lower(m_add(s0, kx[blocksize+8]),  blocksize)
    return [s0]


def tiny_decrypt(ctxt, kx, spice, blocksize, backup):
    """ Encryption of Tiny Subciphers (0 <= blocksize < 36) """

    s0 = ctxt[0]
    for cycle_num in reversed(range(1 + backup)):
        s0 = mask_lower(m_sub(s0, kx[blocksize+8]),blocksize)
        if 1 <= blocksize < 7:
            s0 = tiny_1_6_decrypt(s0, kx, spice, blocksize, cycle_num)
        else:
            temp = []
            for i in range(8):
                temp.append(m_xor(spice[i], kx[4 * blocksize + 16 + i]))
            spice_long = [0, 0, 0, 0, 0, 0, 0, 0]
            temp[0] = m_add(temp[0], cycle_num)
            temp = long_encrypt(temp, kx, spice_long, 512, 0)
            temp.append(temp[7])
            temp.append(temp[7])

            for i in range(8):
                t0 = m_add(m_lsh(temp[8], 21), m_rsh(temp[8], 13))
                temp[8] = m_add(temp[8], m_xor(t0, m_add(temp[i], kx[16+i])))
                temp[9] = m_xor(temp[8], temp[9])
            if 7 <= blocksize <= 15:
                s0 = tiny_7_15_decrypt(s0, temp, kx, blocksize)
            else:
                s0 = tiny_16_35_decrypt(s0, temp, kx, blocksize)

        s0 = mask_lower(m_sub(m_sub(s0, kx[blocksize]), cycle_num), blocksize)
    return [s0]

def _PERM_TINY(N, val): return val >> (mask_lower(N, 4) * 4)
def _PERM1_TINY(N): return _PERM_TINY(N, 0x324f6a850d19e7cb)
def _PERM2_TINY(N): return _PERM_TINY(N, 0x2b7e1568adf09c43)
def _PERM1I_TINY(N): return _PERM_TINY(N, 0xc3610a492b8dfe57)
def _PERM2I_TINY(N): return _PERM_TINY(N, 0x5c62e738d9a10fb4)

def tiny_1_6_encrypt(s0, kx, spice, blocksize, cycle_num):
    assert (1 <= blocksize < 7)
    tmp = []
    tmp.append(kx[16+2*blocksize])
    tmp[0] = m_add(tmp[0], cycle_num)
    tmp.append(kx[17+2*blocksize])
    if blocksize < 5:
        tmp = medium_encrypt(tmp, kx, spice, 128, 0)
        if blocksize == 1:
            N = tmp[1] << 64
            N += (tmp[0] + tmp[1]) & ((1 << 64) - 1)
            #Fibonnaci Folding
            N += N>>89;  N ^= N>>55
            N += N>>34;  N ^= N>>21
            N += N>>13;  N ^= N>>8
            N += N>>5;   N ^= N>>3
            N += N>>2;   N ^= N>>1; N += N>>1
            s0 ^= N & 1
        elif blocksize <= 3:
            for word in tmp:
                for i in range(math.ceil(32/blocksize)):
                    s0 = mask_lower(s0 ^ (word & ((1 << blocksize)-1)), blocksize)
                    word >>= blocksize
                    s0 = mask_lower(s0 + (word & ((1 << blocksize)-1)), blocksize)
                    s0 = m_lrot(s0, 1, blocksize)
                    word >>= blocksize
        else:
            for word in tmp:
                for i in range(math.ceil(32/blocksize)):
                    s0 = _PERM1_TINY(s0 ^ (word & ((1 << blocksize)-1)))
                    word >>= blocksize
                    s0 = _PERM2_TINY(s0 + (word & ((1 << blocksize)-1)))
                    word >>= blocksize
    else:
        tmp.append(kx[18+2*blocksize])
        if blocksize == 6:
            tmp.append(kx[19+2*blocksize])
            tmp.append(kx[20+2*blocksize])
            tmp.append(kx[21+2*blocksize])
            tmp = long_encrypt(tmp, kx, spice, 384, 0)
        else:
            tmp = long_encrypt(tmp, kx, spice, 192, 0)

        for T in tmp:
            for i in range(7 - (1 if blocksize == 6 else 0)):
                s0 = mask_lower(s0 ^ T, blocksize)
                first_four = s0 & 0b1111
                s0 = s0 - first_four
                s0 = s0 + (_PERM1_TINY(first_four) & 0b1111)
                s0 = s0 ^ (s0 >>3)
                s0 = mask_lower(s0 + (T>>blocksize), blocksize)
                first_four = s0 & 0b1111
                s0 = s0 - first_four
                s0 = s0 + (_PERM2_TINY(first_four) & 0b1111)
                T >>= 9
                if blocksize == 6: T >>= 2
    return s0

def tiny_1_6_decrypt(s0, kx, spice, blocksize, cycle_num):
    assert (1 <= blocksize < 7)
    tmp = []
    tmp.append(kx[16+2*blocksize])
    tmp[0] = m_add(tmp[0], cycle_num)
    tmp.append(kx[17+2*blocksize])
    if blocksize < 5:
        tmp = medium_encrypt(tmp, kx, spice, 128, 0)
        m_val = (1 << blocksize*2) - 1
        if blocksize == 1:
            N = tmp[1] << 64
            N += (tmp[0] + tmp[1]) & ((1 << 64) - 1)
            #Fibonnaci Folding
            N += N>>89;  N ^= N>>55
            N += N>>34;  N ^= N>>21
            N += N>>13;  N ^= N>>8
            N += N>>5;   N ^= N>>3
            N += N>>2;   N ^= N>>1; N += N>>1
            s0 ^= N & 1
        elif blocksize <= 3:
            for word in tmp[::-1]:
                for i in reversed(range(math.ceil(32/blocksize))):
                    t_word = (word & (m_val << (i * blocksize * 2))) >> (i * blocksize * 2)
                    s0 = m_rrot(s0, 1, blocksize)
                    s0 = mask_lower(s0 - (t_word >> blocksize), blocksize)
                    s0 = mask_lower(s0 ^ (t_word & ((1 << blocksize)-1)), blocksize)
        else:
            for word in tmp[::-1]:
                for i in reversed(range(math.ceil(32/blocksize))):
                    t_word = (word & (m_val << (i * blocksize * 2))) >> (i * blocksize * 2)
                    s0 = _PERM2I_TINY(s0)
                    s0 -= (t_word >> blocksize)
                    s0 = _PERM1I_TINY(s0)
                    s0 ^= (t_word & ((1 << blocksize)-1))
    else:
        tmp.append(kx[18+2*blocksize])
        if blocksize == 6:
            tmp.append(kx[19+2*blocksize])
            tmp.append(kx[20+2*blocksize])
            tmp.append(kx[21+2*blocksize])
            tmp = long_encrypt(tmp, kx, spice, 384, 0)
        else:
            tmp = long_encrypt(tmp, kx, spice, 192, 0)
        for T in tmp[::-1]:
            t = T
            for i in reversed(range(7 - (1 if blocksize == 6 else 0))):
                first_four = s0 & 0b1111
                s0 = s0 - first_four
                s0 = s0 + (_PERM2I_TINY(first_four) & 0b1111)
                T = t >> 9*i
                if blocksize == 6: T >>= (2*i)
                s0 = mask_lower(s0 - (T>>blocksize), blocksize)
                s0 = s0 ^ (s0 >>3)
                first_four = s0 & 0b1111
                s0 = s0 - first_four
                s0 = s0 + (_PERM1I_TINY(first_four) & 0b1111)
                s0 = mask_lower(s0 ^ T, blocksize)
    return s0

def tiny_7_15_encrypt(s0, temp, kx, blocksize):
    """ Encryption of Tiny SubSubciphers (7 <= blocksize <= 15) """

    assert(7 <= blocksize < 16)
    LBH = (blocksize+1)//2
    for I in range(10):
        nT = temp[I]
        for j in range(int(math.ceil(32/blocksize))):
            T = mask_lower(nT, 2 * blocksize)
            nT >>= (2 * blocksize)
            s0 = m_add(s0, T)
            s0 = mask_lower(m_xor(s0, m_lsh(kx[16*I + (s0&15)], 4)), blocksize)
            s0 = m_rrot(s0, 4, blocksize)
            s0 = m_xor(s0, m_rsh(s0, LBH))
            s0 = m_xor(s0, m_rsh(T, blocksize))
            s0 = m_add(s0, m_lsh(s0, LBH+2))
            s0 = m_xor(s0, Perma[s0&15])
            s0 = m_add(s0, m_lsh(s0, LBH))
    return s0

def tiny_7_15_decrypt(s0, temp, kx, blocksize):
    """ Decryption of Tiny SubSubciphers (7 <= blocksize <= 15) """

    assert(7 <= blocksize < 16)
    LBH = (blocksize+1)//2
    for I in reversed(range(10)):
        num_shifts = int(math.ceil(32/blocksize))
        nT = temp[I] >> (2 * blocksize * (num_shifts-1))
        for j in reversed(range(num_shifts)):
            T = nT & ((1 << (2 * blocksize)) - 1)
            if j != 0:
                nT = temp[I] >> (2 * blocksize * (j-1))
            s0 = m_sub(s0, m_lsh(s0, LBH))
            s0 = m_xor(s0, Permai[s0&15])
            s0 = m_sub(s0, m_lsh(s0, LBH+2))
            s0 = mask_lower(m_xor(s0, m_rsh(T, blocksize)), blocksize)
            s0 = m_xor(s0, m_rsh(s0, LBH))
            s0 = m_lrot(s0, 4, blocksize)
            s0 = mask_lower(m_xor(s0, m_lsh(kx[16*I + (s0&15)], 4)), blocksize)
            s0 = m_sub(s0, T)
    return s0

def tiny_16_35_encrypt(s0, temp, kx, blocksize):
    """ Encryption of Tiny SubSubciphers (16 <= blocksize <= 35) """

    assert(16 <= blocksize <= 35)
    for T in temp:
        for j in range(int(math.ceil(64/blocksize))):
            s0 = m_add(s0, T)
            s0 = m_xor(s0, m_lsh(kx[s0&255], 8))
            s0 = mask_lower(s0, blocksize)
            s0 = m_rrot(s0, 8, blocksize)
            T = m_rsh(T, blocksize)
    return s0

def tiny_16_35_decrypt(s0, temp, kx, blocksize):
    """ Decryption of Tiny SubSubciphers (16 <= blocksize <= 35) """

    assert(16 <= blocksize <= 35)
    for tt in temp[::-1]:
        for j in reversed(range(int(math.ceil(64/blocksize)))):
            T = m_rsh(tt, blocksize*j)
            s0 = m_lrot(s0, 8, blocksize)
            s0 = m_xor(s0, m_lsh(kx[s0&255], 8))
            s0 = mask_lower(s0, blocksize)
            s0 = mask_lower(m_sub(s0, T), blocksize)
    return s0

def long_encrypt(s, kx, spice, blocksize, backup, lmask=None):
    """ Encryption of Long Subciphers (128 < blocksize < 513) """

    if not lmask: lmask = (1 << 64) - 1

    for cycle_num in range(backup + 1):
        for i in range(len(s)-1):
            s[i] = m_add(s[i], kx[(blocksize&255)+i])
        s[0] = m_add(s[0], cycle_num)
        s[-1] = m_add(s[-1], kx[(blocksize&255)+7])&lmask
        for i in range(8):
            t = s[0]&255
            k = kx[t]
            kk = kx[t+3*i+1]
            s[1] = m_add(s[1], k)
            s[0] = m_xor(s[0], m_lsh(kk, 8))
            kk = m_xor(kk, k)
            s[1] = m_add(s[1], m_rsh(kk, 5))
            s[0] = m_sub(s[0], m_lsh(kk, 12))
            s[-1] = m_add(s[-1], kk)&lmask
            s[-1] = m_xor(s[-1], s[0])&lmask
            s[1] = m_add(s[1], s[-1])
            s[1] = m_xor(s[1], m_lsh(s[-1], 13))
            s[0] = m_sub(s[0], m_rsh(s[-1], 11))
            s[0] = m_add(s[0], spice[i])
            s[1] = m_xor(s[1], spice[i^1])
            s[0] = m_add(s[0], m_lsh(s[1], 9+i))
            s[1] = m_add(s[1], m_xor(m_rsh(s[0], 3), IRN1 + blocksize))
            s[0] = m_xor(s[0], m_rsh(s[1], 4))
            s[0] = m_add(s[0], spice[i^2])
            t = spice[i^4]
            s[1] = m_add(s[1], t)
            s[1] = m_xor(s[1], m_rsh(t, 3))
            s[1] = m_sub(s[1], m_lsh(t, 5))
            s[0] = m_xor(s[0], s[1])
            if blocksize > 448:
                s[6] = m_add(s[6], s[0])
                s[6] = m_xor(s[6], m_lsh(s[3], 11))
                s[1] = m_add(s[1], m_rsh(s[6], 13))
                s[6] = m_add(s[6], m_lsh(s[5], 7))
                s[4] = m_xor(s[4], s[6])

            if blocksize > 384:
                s[5] = m_xor(s[5], s[1])
                s[5] = m_add(s[5], m_lsh(s[4], 15))
                s[0] = m_sub(s[0], m_rsh(s[5], 7))
                s[5] = m_xor(s[5], m_rsh(s[3], 9))
                s[2] = m_xor(s[2], s[5])
            if blocksize > 320:
                s[4] = m_sub(s[4], s[2])
                s[4] = m_xor(s[4], m_rsh(s[1], 10))
                s[0] = m_xor(s[0], m_lsh(s[4], 3))
                s[4] = m_sub(s[4], m_lsh(s[2], 6))
                s[3] = m_add(s[3], s[4])
            if blocksize > 256:
                s[3] = m_xor(s[3], s[2])
                s[3] = m_sub(s[3], m_rsh(s[0], 7))
                s[2] = m_xor(s[2], m_lsh(s[3], 15))
                s[3] = m_xor(s[3], m_lsh(s[1], 5))
                s[1] = m_add(s[1], s[3])

            if blocksize > 192:
                s[2] = m_xor(s[2], s[1])
                s[2] = m_add(s[2], m_lsh(s[0], 13))
                s[1] = m_sub(s[1], m_rsh(s[2], 5))
                s[2] = m_sub(s[2], m_rsh(s[1], 8))
                s[0] = m_xor(s[0], s[2])

            s[1] = m_xor(s[1], kx[(blocksize + 17 + (i<<5))&255])
            s[1] = m_add(s[1], m_lsh(s[0], 19))
            s[0] = m_sub(s[0], m_rsh(s[1], 27))
            s[1] = m_xor(s[1], spice[i^7])
            s[-1] = m_sub(s[-1], s[1])&lmask
            s[0] = m_add(s[0], m_and(s[1], m_rsh(s[1], 5)))
            s[1] = m_xor(s[1], m_rsh(s[0], s[0] & 31))
            s[0] = m_xor(s[0], kx[s[1]&255])


        for i in range(len(s)-1):
            s[i] = m_add(s[i], kx[(blocksize&255)+8+i]) #change from spec
        s[-1] = m_add(s[-1], kx[(blocksize&255)+15])&lmask # change from spec

    return s


def long_decrypt(s, kx, spice, blocksize, backup, lmask=None):
    """ Decryption of Long Subciphers (128 < blocksize < 513) """

    if not lmask: lmask = (1 << 64) - 1

    for cycle_num in reversed(range(backup + 1)):
        for i in range(len(s)-1):
            s[i] = m_sub(s[i], kx[(blocksize&255)+8+i]) #change from spec
        s[-1] = m_sub(s[-1], kx[(blocksize&255)+15])&lmask # change from spec

        for i in reversed(range(8)):
            s[0] = m_xor(s[0], kx[s[1]&255])
            s[1] = m_xor(s[1], m_rsh(s[0], s[0] & 31))
            s[0] = m_sub(s[0], m_and(s[1], m_rsh(s[1], 5)))
            s[-1] = m_add(s[-1], s[1])&lmask
            s[1] = m_xor(s[1], spice[i^7])
            s[0] = m_add(s[0], m_rsh(s[1], 27))
            s[1] = m_sub(s[1], m_lsh(s[0], 19))
            s[1] = m_xor(s[1], kx[(blocksize + 17 + (i<<5))&255])

            if blocksize > 192:
                s[0] = m_xor(s[0], s[2])
                s[2] = m_add(s[2], m_rsh(s[1], 8))
                s[1] = m_add(s[1], m_rsh(s[2], 5))
                s[2] = m_sub(s[2], m_lsh(s[0], 13))
                s[2] = m_xor(s[2], s[1])

            if blocksize > 256:
                s[1] = m_sub(s[1], s[3])
                s[3] = m_xor(s[3], m_lsh(s[1], 5))
                s[2] = m_xor(s[2], m_lsh(s[3], 15))
                s[3] = m_add(s[3], m_rsh(s[0], 7))
                s[3] = m_xor(s[3], s[2])

            if blocksize > 320:
                s[3] = m_sub(s[3], s[4])
                s[4] = m_add(s[4], m_lsh(s[2], 6))
                s[0] = m_xor(s[0], m_lsh(s[4], 3))
                s[4] = m_xor(s[4], m_rsh(s[1], 10))
                s[4] = m_add(s[4], s[2])

            if blocksize > 384:
                s[2] = m_xor(s[2], s[5])
                s[5] = m_xor(s[5], m_rsh(s[3], 9))
                s[0] = m_add(s[0], m_rsh(s[5], 7))
                s[5] = m_sub(s[5], m_lsh(s[4], 15))
                s[5] = m_xor(s[5], s[1])

            if blocksize > 448:
                s[4] = m_xor(s[4], s[6])
                s[6] = m_sub(s[6], m_lsh(s[5], 7))
                s[1] = m_sub(s[1], m_rsh(s[6], 13))
                s[6] = m_xor(s[6], m_lsh(s[3], 11))
                s[6] = m_sub(s[6], s[0])

            t = spice[i^4]
            s[0] = m_xor(s[0], s[1])
            s[1] = m_add(s[1], m_lsh(t, 5))
            s[1] = m_xor(s[1], m_rsh(t, 3))
            s[1] = m_sub(s[1], t)
            s[0] = m_sub(s[0], spice[i^2])
            s[0] = m_xor(s[0], m_rsh(s[1], 4))
            s[1] = m_sub(s[1], m_xor(m_rsh(s[0], 3), IRN1 + blocksize))
            s[0] = m_sub(s[0], m_lsh(s[1], 9+i))
            s[1] = m_xor(s[1], spice[i^1])
            s[0] = m_sub(s[0], spice[i])
            s[0] = m_add(s[0], m_rsh(s[-1], 11))
            s[1] = m_xor(s[1], m_lsh(s[-1], 13))
            s[1] = m_sub(s[1], s[-1])
            s[-1] = m_xor(s[-1], s[0])&lmask
            t = s[0]&255
            k = kx[t]
            kk = kx[t+3*i+1]
            kk = m_xor(kk, k)
            s[-1] = m_sub(s[-1], kk)&lmask
            s[0] = m_add(s[0], m_lsh(kk, 12))
            s[1] = m_sub(s[1], m_rsh(kk, 5))
            kk = m_xor(kk, k)
            s[0] = m_xor(s[0], m_lsh(kk, 8))
            s[1] = m_sub(s[1], k)

        s[0] = m_sub(s[0], cycle_num)

        for i in range(len(s)-1):
            s[i] = m_sub(s[i], kx[(blocksize&255)+i])
        s[-1] = m_sub(s[-1], kx[(blocksize&255)+7])&lmask

    return s

def medium_encrypt(ptxt, kx, spice, blocksize, backup, lmask=None):
    """ Encryption of Medium Subciphers (64 < blocksize < 129) """

    if lmask == 0 or lmask == None: lmask = (1 << 64) - 1

    for cycle_num in range(backup + 1):
        s0 = m_add(m_add(ptxt[0], kx[blocksize]), cycle_num)
        s1 = m_add(ptxt[1], kx[blocksize+1]) & lmask
        for i in range(8):
            k = kx[s0&255]
            s1 = m_add(s1, k) & lmask
            s0 = m_xor(s0, m_lsh(k, 8))
            s1 = m_xor(s1, s0) & lmask
            s0 = m_sub(s0, m_rsh(s1, 11))
            s0 = m_xor(s0, m_lsh(s1, 2))
            s0 = m_sub(s0, spice[i^4])
            s0 = m_add(s0, m_xor(m_lsh(s0, 32), m_add(IRN1, blocksize)))
            s0 = m_xor(s0, m_rsh(s0, 17))
            s0 = m_xor(s0, m_rsh(s0, 34))
            t = spice[i]
            s0 = m_xor(s0, t)
            s0 = m_add(s0, m_lsh(t, 5))
            t = m_rsh(t, 4)
            s1 = m_add(s1, t) & lmask
            s0 = m_xor(s0, t)
            s0 = m_add(s0, m_lsh(s0, 22 + (s0&31)))
            s0 = m_xor(s0, m_rsh(s0, 23))
            s0 = m_sub(s0, spice[i^7])
            t = s0&255
            k = kx[t]
            kk = kx[t+3*i+1]
            s1 = m_xor(s1, k) & lmask
            s0 = m_xor(s0, m_lsh(kk, 8))
            kk = m_xor(kk, k)
            s1 = m_add(s1, m_rsh(kk, 5)) & lmask
            s0 = m_sub(s0, m_lsh(kk, 12))
            s0 = m_xor(s0, kk &~ 255)
            s1 = m_add(s1, s0) & lmask
            s0 = m_add(s0, m_lsh(s1, 3))
            s0 = m_xor(s0, spice[i^2])
            s0 = m_add(s0, kx[blocksize+16+i])
            s0 = m_add(s0, m_lsh(s0, 22))
            s0 = m_xor(s0, m_rsh(s1, 4))
            s0 = m_add(s0, spice[i^1])
            s0 = m_xor(s0, m_rsh(s0, 33+i))

        ptxt[0] = m_add(s0, kx[blocksize+8])
        ptxt[1] = m_add(s1, kx[blocksize+9]) & lmask

    return ptxt

""" Decryption of Medium Subciphers (64 < blocksize < 129) """
def medium_decrypt(ctxt, kx, spice, blocksize, backup, lmask=None):
    if lmask == 0 or lmask == None: lmask = (1 << 64) - 1

    for cycle_num in reversed(range(backup + 1)):
        s0 = m_sub(ctxt[0], kx[blocksize+8])
        s1 = m_sub(ctxt[1], kx[blocksize+9]) & lmask
        i = 7
        while (i >= 0):
            t = s0
            t = m_rsh(t, 33+i)
            s0 = m_xor(s0, t)
            s0 = m_sub(s0, spice[i^1])
            t = s1
            t = m_rsh(t, 4)
            s0 = m_xor(s0, t)
            k = s0
            k = m_lsh(k, 22)
            t = s0
            t = m_sub(t, k)
            t = m_lsh(t, 22)
            s0 = m_sub(s0, t)
            s0 = m_sub(s0, kx[blocksize+16+i])
            s0 = m_xor(s0, spice[i^2])
            t = s1
            t = m_lsh(t, 3)
            s0 = m_sub(s0, t)
            s1 = m_sub(s1, s0) & lmask
            tt = s0&255;
            k = kx[tt]
            tt += 3 * i + 1
            kk = kx[tt]
            kk = m_xor(kk, k)
            t = kk & ~255
            s0 = m_xor(s0, t)
            t = kk
            t = m_lsh(t, 12)
            s0 = m_add(s0, t)
            t = kk
            t = m_rsh(t, 5)
            s1 = m_sub(s1, t) & lmask
            kk = kx[tt]
            kk = m_lsh(kk, 8)
            s0 = m_xor(s0, kk)
            s1 = m_xor(s1, k) & lmask
            s0 = m_add(s0, spice[i^7])
            t = s0
            t = m_rsh(t, 23)
            s0 = m_xor(s0, t)
            t = s0
            t = m_rsh(t, 46)
            s0 = m_xor(s0, t)
            tt = 22 + (s0 & 31)
            t = s0
            t = m_lsh(t, tt)
            kk = s0
            kk = m_sub(kk, t)
            kk = m_lsh(kk, tt)
            s0 = m_sub(s0, kk)
            kk = spice[i]
            t = kk
            kk = m_rsh(kk, 4)
            s0 = m_xor(s0, kk)
            s1 = m_sub(s1, kk) & lmask
            k = t
            k = m_lsh(k, 5)
            s0 = m_sub(s0, k)
            s0 = m_xor(s0, t)
            t = s0
            t = m_rsh(t, 17)
            s0 = m_xor(s0, t)
            t = IRN1 + blocksize
            k = s0
            k = m_sub(k, t)
            k = m_lsh(k, 32)
            t = m_xor(t, k)
            s0 = m_sub(s0, t)
            s0 = m_add(s0, spice[i^4])
            t = s1
            t = m_lsh(t, 2)
            s0 = m_xor(s0, t)
            t = s1
            t = m_rsh(t, 11)
            s0 = m_add(s0, t)
            s1 = m_xor(s1, s0) & lmask
            tt = s0 & 255
            k = kx[tt]
            t = k
            t = m_lsh(t, 8)
            s0 = m_xor(s0, t)
            s1 = m_sub(s1, k) & lmask
            i -= 1

        ctxt[0] = m_sub(m_sub(s0, kx[blocksize]), cycle_num)
        ctxt[1] = m_sub(s1, kx[blocksize+1]) & lmask

    return ctxt

SWIZ_POLY_NUMBERS = [0, 3, 7, 0xb, 0x13, 0x25, 0x43, 0x83, 0x11d, 0x211, 0x409,
     0x805, 0x1053, 0x201b, 0x402b, 0x8003, 0x1002d, 0x20009,
     0x40027, 0x80027, 0x100009, 0x200005, 0x400003, 0x800021,
     0x100001b, 0x2000009, 0x4000047, 0x8000027, 0x10000009,
     0x20000005, 0x40000053, 0x80000009]

def extended_encrypt(ptxt, kx, spice, blocksize, backup, lmask=None):
    """ Encryption of Extended Subciphers (blocksize > 512) """

    if not lmask: lmask = (1 << 64) - 1

    LWD = int(math.ceil(blocksize/64))
    QMSK = math.pow(2, math.ceil(math.log(LWD, 2))) - 1
    SWZ = 0
    for num in SWIZ_POLY_NUMBERS:
        if num > QMSK: SWZ = num; break

    s = []
    for i in range(8):
        s.append(m_add(ptxt[i], kx[(blocksize&255)+i]))

    # pre mix
    for i in range(3): #CHANGE FROM SPEC
        _stir_extended(s, i, (1 << 64) - 1, kx, spice)

    for i in range(8, len(ptxt)):
        ptxt[7] = s[7]
        mask = (lmask if i == len(ptxt) -1 else (1 << 64) - 1)
        s[7] = ptxt[i] & mask
        _stir_extended(s, 0, mask, kx, spice)
        ptxt[i] = s[7]
        s[7] = ptxt[7]

    # intermission
    _stir_extended(s, 0, (1 << 64) - 1, kx, spice)
    s[0] += blocksize
    for i in range(2):
        _stir_extended(s, i, (1 << 64) - 1, kx, spice)
    s[0] += blocksize
    ptxt[7] = s[7]

    # second pass
    Qnew = 0
    inside = False
    while Qnew != 0 or not inside:
        inside = True
        Qnew = 5 * Qnew + 1
        Qnew &= int(QMSK)
        if not (Qnew < 8 or Qnew >= LWD):
            s[7] = ptxt[Qnew]
            mask = (lmask if Qnew == len(ptxt) -1 else (1 << 64) - 1)
            _stir_extended(s, 0, mask, kx, spice)
            ptxt[Qnew] = s[7]

    # intermission
    s[7] = ptxt[7]
    _stir_extended(s, 1, (1 << 64) - 1, kx, spice)
    s[0] += blocksize
    for i in range(2): #change in spec
        _stir_extended(s, i, (1 << 64) - 1, kx, spice)
    s[0] += blocksize
    ptxt[7] = s[7]

    #pass 3 iteration method
    Qnew = 1
    QMSK += 1
    inside = False
    while Qnew != 1 or not inside:
        inside = True
        Qnew <<= 1
        if Qnew & int(QMSK): Qnew ^= SWZ
        if not(Qnew < 8 or Qnew >= LWD):
            s[7] = ptxt[Qnew]
            mask = (lmask if Qnew == len(ptxt) -1 else (1 << 64) - 1)
            _stir_extended(s, 0, mask, kx, spice)
            ptxt[Qnew] = s[7]

    # finale
    s[7] = ptxt[7]
    _stir_extended(s, 0, (1 << 64) - 1, kx, spice)

    for i in range(3):
        _stir_extended(s, i, (1 << 64) - 1, kx, spice)

    for i in range(8):
        ptxt[i] = m_add(s[i], kx[(blocksize&255)+i+8])

    return ptxt

def extended_decrypt(ctxt, kx, spice, blocksize, backup, lmask=None):
    """ Decryption of Extended Subciphers (blocksize > 512) """

    if not lmask: lmask = (1 << 64) - 1

    LWD = int(math.ceil(blocksize/64))
    QMSK = math.pow(2, math.ceil(math.log(LWD, 2))) - 1
    SWZ = 0
    for num in SWIZ_POLY_NUMBERS:
        if num > QMSK: SWZ = num; break

    s = []
    for i in range(8):
        s.append(m_sub(ctxt[i], kx[(blocksize&255)+i+8]))

    for i in reversed(range(3)):
        _stir_inverse_extended(s, i, (1 << 64) - 1, kx, spice)

    _stir_inverse_extended(s, 0, (1 << 64) - 1, kx, spice)
    ctxt[7] = s[7]

    Qnew = 1
    QMSK += 1
    inside = False
    while Qnew != 1 or not inside:
        inside = True
        if Qnew & 1: Qnew ^= SWZ;
        Qnew >>= 1
        if Qnew < 8 or Qnew >= LWD: continue
        else:
            s[7] = ctxt[Qnew]
            mask = (lmask if int(Qnew) == len(ctxt) -1 else (1 << 64) - 1)
            _stir_inverse_extended(s, 0, mask, kx, spice)
            ctxt[Qnew] = s[7]

    s[7] = ctxt[7]
    s[0] -= blocksize

    for i in reversed(range(2)): #change in spec
        _stir_inverse_extended(s, i, (1 << 64) - 1, kx, spice)
    s[0] -= blocksize

    _stir_inverse_extended(s, 1, (1 << 64) - 1, kx, spice)

    ctxt[7] = s[7]

    # second pass
    Qnew = 0
    QMSK -= 1
    inside = False
    while Qnew != 0 or not inside:
        inside = True
        Q = Qnew-1
        QQ = Q<<2; QQ += QQ<<1; QQ += QQ<<4; QQ += QQ<<8; QQ += QQ<<16
        Qnew = (Q+QQ) & int(QMSK)
        if Qnew < 8 or Qnew >= LWD: continue
        else:
            s[7] = ctxt[Qnew]
            mask = (lmask if Qnew == len(ctxt) -1 else (1 << 64) - 1)
            _stir_inverse_extended(s, 0, mask, kx, spice)
            ctxt[Qnew] = s[7]

     # intermission
    s[7] = ctxt[7]
    s[0] -= blocksize
    for i in reversed(range(2)):
        _stir_inverse_extended(s, i, (1 << 64) - 1, kx, spice)
    s[0] -= blocksize
    _stir_inverse_extended(s, 0, (1 << 64) - 1, kx, spice)

    # pre mix
    for i in reversed(range(8, len(ctxt))):
        ctxt[7] = s[7]
        mask = (lmask if i == len(ctxt) -1 else (1 << 64) - 1)
        s[7] = ctxt[i] & mask
        _stir_inverse_extended(s, 0, mask, kx, spice)
        ctxt[i] = s[7]
        s[7] = ctxt[7]

    for i in reversed(range(3)): #CHANGE FROM SPEC
        _stir_inverse_extended(s, i, (1 << 64) - 1, kx, spice)

    for i in range(8):
        ctxt[i] = m_sub(s[i], kx[(blocksize&255)+i])

    return ctxt

def _stir_extended(s, i, mask, kx, spice):
    t = s[0] & 255
    k = kx[t]
    kk = kx[t+1+(i<<2)]
    s[3] = m_add(s[3], s[7])
    s[5] = m_xor(s[5], s[7])
    s[1] = m_add(s[1], k)
    s[2] = m_xor(s[2], k)
    s[4] = m_add(s[4], kk)
    s[6] = m_xor(s[6], kk)
    s[4] = m_xor(s[4], s[1])
    s[5] = m_add(s[5], s[2])
    s[0] = m_xor(s[0], s[5]>>13)
    s[1] = m_sub(s[1], s[6]>>22)
    s[2] = m_xor(s[2], s[7]<<7)

    s[7] = m_xor(s[7], s[6]<<9)
    s[7] = m_add(s[7], s[0]) & mask

    t = s[1] & 31
    tt = s[1]>>t
    ttt = s[2]<<t

    s[3] = m_add(s[3], ttt)
    s[4] = m_sub(s[4], s[0])
    s[5] = m_xor(s[5], ttt)
    s[6] = m_xor(s[6], tt)
    s[7] = m_add(s[7], tt) & mask

    t = s[4]>>t
    s[2] = m_sub(s[2], t)
    s[5] = m_add(s[5], t)

    if i == 1:
        s[0] += spice[0]; s[1] ^= spice[1]; s[2] -= spice[2]; s[3] ^=spice[3]
        s[4] = m_add(s[4], spice[4]); s[5] ^= spice[5]; s[6] -= spice[6]; s[7] = m_xor(s[7] & mask, spice[7]) & mask

    s[7] = m_sub(s[7], s[3]) & mask
    s[1] = m_xor(s[1], (s[7]>>11))
    s[6] = m_add(s[6], s[3])
    s[0] = m_xor(s[0], s[6])
    t = m_xor(s[2], s[5])
    s[3] = m_sub(s[3], t)
    t &= 0x5555555555555555
    s[2] = m_xor(s[2], t);  s[5] = m_xor(s[5], t)
    s[0] = m_add(s[0], t)
    t = m_lsh(s[4], 9)
    s[6] = m_sub(s[6], t)
    s[1] = m_add(s[1], t)

def _stir_inverse_extended(s, i, mask, kx, spice):

    t = m_lsh(s[4], 9)
    s[1] = m_sub(s[1], t)
    s[6] = m_add(s[6], t)

    t = m_xor(s[2], s[5])
    s[3] = m_add(s[3], t)
    t &= 0x5555555555555555
    s[2] = m_xor(s[2], t);  s[5] = m_xor(s[5], t)
    s[0] = m_sub(s[0], t)

    s[0] = m_xor(s[0], s[6])
    s[6] = m_sub(s[6], s[3])
    s[1] = m_xor(s[1], (s[7]>>11))

    s[7] = m_add(s[7], s[3]) & mask

    if i == 1:
        s[0] = m_sub(s[0], spice[0])
        s[1] = m_xor(s[1], spice[1])
        s[2] = m_add(s[2], spice[2])
        s[3] = m_xor(s[3], spice[3])
        s[4] = m_sub(s[4], spice[4])
        s[5] = m_xor(s[5], spice[5])
        s[6] = m_add(s[6], spice[6])
        s[7] = m_xor(s[7] & mask, spice[7])

    t = m_rsh(s[4], (s[1] & 31))
    s[5] = m_sub(s[5], t)
    s[2] = m_add(s[2], t)
    t = s[1] & 31
    tt = s[1]>>t
    ttt = s[2]<<t

    s[3] = m_sub(s[3], ttt)
    s[4] = m_add(s[4], s[0])
    s[5] = m_xor(s[5], ttt)
    s[6] = m_xor(s[6], tt)
    s[7] = m_sub(s[7], tt) & mask

    t = s[0] & 255
    k = kx[t]
    kk = kx[t+1+(i<<2)]

    s[7] = m_sub(s[7], s[0])
    s[7] = m_xor(s[7], s[6]<<9) & mask

    s[2] = m_xor(s[2], s[7]<<7)
    s[1] = m_add(s[1], s[6]>>22)
    s[0] = m_xor(s[0], s[5]>>13)

    t = s[0] & 255
    k = kx[t]
    kk = kx[t+1+(i<<2)]

    s[5] = m_sub(s[5], s[2])
    s[4] = m_xor(s[4], s[1])
    s[6] = m_xor(s[6], kk)
    s[4] = m_sub(s[4], kk)
    s[2] = m_xor(s[2], k)
    s[1] = m_sub(s[1], k)
    s[5] = m_xor(s[5], s[7])
    s[3] = m_sub(s[3], s[7])

def stir(kx):
    """
    The purpose of the Stirring function is to psuedo-randomize the kx array,
    allowing each bit to influence every other bit.

    Args:
        kx: key expansion table

    """
    # define internal state variables
    s = []
    for i in range(248, 256):
        s.append(kx[i])

    for j in range(NUM_STIR_PASSES + BACKUP + BACKUPSUBCIPHER[0]):
        for i in range(256):
            s[0] = m_xor(s[0], m_add(m_xor(kx[i], kx[(i+83) & 255]), kx[s[0] & 255]))
            s[2] = m_add(s[2], kx[i]) # fix for Wagner equivalent problem
            s[1] = m_add(s[0], s[1])
            s[3] = m_xor(s[3], s[2])
            s[5] = m_sub(s[5], s[4])
            s[7] = m_xor(s[7], s[6])
            s[3] = m_add(s[3], m_rsh(s[0], 13))
            s[4] = m_xor(s[4], m_lsh(s[1], 11))
            s[5] = m_xor(s[5], m_lsh(s[3], m_and(s[1], 31)))
            s[6] = m_add(s[6], m_rsh(s[2], 17))
            s[7] = m_or(s[7], m_add(s[3], s[4]))
            s[2] = m_sub(s[2], s[5])
            s[0] = m_sub(s[0], m_xor(s[6], i))
            s[1] = m_xor(s[1], m_add(s[5], IRN1))
            s[2] = m_add(s[2], m_rsh(s[7], j))
            s[2] = m_xor(s[2], s[1])
            s[4] = m_sub(s[4], s[3])
            s[6] = m_xor(s[6], s[5])
            s[0] = m_add(s[0], s[7])
            kx[i] = m_add(s[2], s[6])

def _display(kx):
    """ Helper function to display key expansion table"""

    print_kx = kx[:256]
    for i, k in enumerate(print_kx):
        print(hex(k), end='\t\n' if (i+1) % 8 == 0 else '\t')

def hex_output(s):
    return "0x" + "".join(["%016x" % x for x in s]) if s else None

class SubCipher(Enum):
    tiny = 1
    short = 2
    medium = 3
    long = 4
    extended = 5

def getSubCiphNum(blocksize):
    """ Maps sub cipher number to block size """

    if blocksize < 36:
        return SubCipher.tiny
    elif blocksize < 65:
        return SubCipher.short
    elif blocksize < 129:
        return SubCipher.medium
    elif blocksize < 513:
        return SubCipher.long
    else:
        return SubCipher.extended

def encrypt(ptxt, kx, spice, blocksize, backup=0):
    """ Main encryption function

    Args:
        ptxt: plaintext
        kx: key expansion table
        spice: spice
        blocksize: size of block
        backup: value for backup

    Returns:
        Encrypted plaintext

    """

    temp_ptxt = ptxt
    if type(spice) != str: spice = hex(spice)
    spice = hex_str_to_arr(spice, 128)
    if type(ptxt) != str: temp_ptxt = hex(ptxt)
    ptxt_arr = hex_str_to_arr(temp_ptxt)
    lmask = (1 << blocksize % 64) - 1
    args = (ptxt_arr, kx, spice, blocksize, backup)
    if blocksize < 36:
        s = tiny_encrypt(*args)
    elif blocksize < 65:
        s = short_encrypt(*args, lmask)
    elif blocksize < 129:
        s = medium_encrypt(*args, lmask)
    elif blocksize < 513:
        s = long_encrypt(*args, lmask)
    else:
        s = extended_encrypt(*args, lmask)

    hex_result = hex_output(s)
    if type(ptxt) == str: return hex_result
    return int(hex_result, 16)

def decrypt(ctxt, kx, spice, blocksize, backup=0):
    """ Main decryption function

        Args:
            ctxt: ciphertext
            kx: key expansion table
            spice: spice
            blocksize: size of block
            backup: value for backup

        Returns:
            Decrypted ciphertext

        """

    temp_ctxt = ctxt
    if type(spice) != str: spice = hex(spice)
    elif spice[0:2] != "0x": spice = hex(_string_to_hex(spice))
    spice = hex_str_to_arr(spice, 128)
    if type(ctxt) != str: temp_ctxt = hex(ctxt)
    elif ctxt[0:2] != "0x": temp_ctxt = hex(_string_to_hex(ctxt))
    ctxt_arr = hex_str_to_arr(temp_ctxt)
    args = (ctxt_arr, kx, spice, blocksize, backup)
    lmask = (1 << blocksize % 64) - 1
    if blocksize < 36:
        s = tiny_decrypt(*args)
    elif blocksize < 65:
        s = short_decrypt(*args, lmask)
    elif blocksize < 129:
        s = medium_decrypt(*args, lmask)
    elif blocksize < 513:
        s = long_decrypt(*args, lmask)
    else:
        s = extended_decrypt(*args, lmask)
    hex_result = hex_output(s)
    if type(ctxt) == str: return hex_result
    return int(hex_result, 16)

def generate_hpc_functions(key, blocksize, key_length, backup):
    """ Generates encryption and decryption functions """

    kx_table = create_kx_table(key, getSubCiphNum(blocksize).value, key_length)
    def encrypt_f(ptxt, spice):
        assert(get_blocksize_from_hex(ptxt) <= blocksize)
        return encrypt(ptxt, kx_table, spice, blocksize, backup)
    def decrypt_f(ctxt, spice):
        assert(get_blocksize_from_hex(ctxt) <= blocksize)
        return decrypt(ctxt, kx_table, spice, blocksize, backup)
    return encrypt_f, decrypt_f

def get_blocksize_from_hex(hex_val):
    if type(hex_val) == str:
        hex_val = int(hex_val, 16)
    return len(bin(hex_val)) - 2

def _string_to_hex(s):
    str(_bytes_to_string(hexlify(bytes(s, 'utf-8'))), 'utf-8')
