# xmss-jasmin

## Proofs (for XMSSMT-SHA2_20/2_256)

Run

```bash
make -C proof/ check_spec
make -C proof/ check_xmss_xmssmt_proof
make -j$(nproc) -C proof/ check_correctness_proof
make -j$(nproc) -C proof/ check_correctness_proof ECADDFLAGS="-pragmas Proofs:weak"
```

Or, using docker

```bash
docker build -t jasmin-xmss .
docker run --rm -it jasmin-xmss
```

and then

```bash
make -C proof/ check_spec
make -C proof/ check_xmss_xmssmt_proof
make -j$(nproc) -C proof/ check_correctness_proof
make -j$(nproc) -C proof/ check_correctness_proof ECADDFLAGS="-pragmas Proofs:weak"
```
