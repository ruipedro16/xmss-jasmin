# xmss-jasmin

Antes: 1.38s
Depois: .41s
Diferenca: ((1.38-.41) / 1.38) * 100 = 70.3%

## Reference Implementation

```
Benchmarking variant XMSSMT-SHA2_20/2_256
Generating keypair.. took 1378389.257000 us (1.38 sec), 3599387881 cycles
Creating 16 signatures..
        median        : 7042398485 cycles
        average       : 7045889996 cycles

Verifying 16 signatures..
        median        : 3831887 cycles
        average       : 3903214 cycles

Signature size: 4963 (4.85 KiB)
Public key size: 64 (0.06 KiB)
Secret key size: 131 (0.13 KiB)
```

## Reference Implementation Using Implementation of SHA-2 with [Intel SHA Extensions](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sha-extensions.html)

```
Benchmarking variant XMSSMT-SHA2_20/2_256
Generating keypair.. took 407045.399000 us (0.41 sec), 1062961659 cycles
Creating 16 signatures..
        median        : 2115588080 cycles
        average       : 2118018349 cycles

Verifying 16 signatures..
        median        : 1083017 cycles
        average       : 1083068 cycles

Signature size: 4963 (4.85 KiB)
Public key size: 64 (0.06 KiB)
Secret key size: 131 (0.13 KiB)
```