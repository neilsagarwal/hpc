# Hasty Pudding Cipher

## Introduction

This repository provides an implementation of the Hasty Pudding Cipher in Python.

Hasty Pudding Cipher (HPC) was designed by Richard Schroeppel for the AES competition. HPC is an example of a '[tweakable block cipher][tweakable_block_cipher]', a cipher that takes in a secondary "lightweight" key (a tweak) for further entropy.

The implementation was derived from the publicly available [HPC specification][hpc_specification].

## Python

Sample Usage:

```python
from hpc import generate_hpc_functions

blocksize = 125
key_length = 128
key = 0xf3aef8062681d980c14bd5915305f319

# generate cipher functions
encrypt, decrypt = generate_hpc_functions(key, blocksize, key_length, backup)

ptxt = 0x0000000000000079
spice = 0x4957df9f02329f2d07289bb61a440e059f9c5dcb93048b5686208a26403c5e7f706d0051cdb0d7bb8f0c6e4962e43023a0b02b363ffa0b53abf6d3f4f848f5e9

# encrypt value
encrypted_value = encrypt(ptxt, spice)
print("Encryption of %s: %s" % (ptxt, encrypted_value))

# decrypt value
decrypted_value = decrypt(encrypted_value, spice)
print("Decryption of %s: %s" % (encrypted_value, decrypted_value))
```

[tweakable_block_cipher]: https://people.eecs.berkeley.edu/~daw/papers/tweak-crypto02.pdf
[hpc_specification]: http://richard.schroeppel.name:8015/hpc/hpc-spec
