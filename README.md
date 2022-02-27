Generate MICE traces from Decision-DNNFs.
=========================================

Decision-DNNFs are accepted in the format 
generated by D4 (https://github.com/crillab/d4).

Generate a Decision-DNNFs with:
```
./d4 -dDNNF test.cnf -out=/tmp/test.nnf
```

Then generate a trace with
```
cargo run --release -- test.cnf /tmp/test.nnf  > trace
```

Use https://github.com/vroland/sharptrace to check trace correctness.
