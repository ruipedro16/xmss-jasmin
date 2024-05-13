# xmss-jasmin

```
git clone --recurse-submodules git@github.com:ruipedro16/xmss-jasmin.git
```

### Tests 

```
cd test/xmss && make run # Only tests XMSS
cd test/ && ./run_all_tests.sh
```

### Benchmarks

```
cd bench && make run
```

### Proofs

```
cd spec && make all
```

### Docker

```
docker build -t xmss-jasmin .
docker run -it xmss-jasmin bash
```