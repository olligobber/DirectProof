# Direct Proof

Create direct proofs automatically.

## Usage

Once compiled, main can accept a conclusion followed by assumptions as command line arguments, or be run in interactive mode.

Example usage:

```
$ ./main "B" "A" "A->B"
 1 |             A             | Assumption
 2 |           (A→B)           | Assumption
...
22 |             B             | Simplification 21
```

```
$ ./main "A" "B" "A->B"
Cannot be proven, due to the following boolean
assignment being a counter-example:
A ↦ False
B ↦ True
```

```
$ ./main "B\/~B" "A"
Cannot be proven directly, due to the following
3-valued assignment being a counter-example:
A ↦ True
B ↦ Unknown
```

```
$ ./main help
To use command line arguments, provide the conclusion
as the first argument, and the assumptions as the rest
Conclusion: a & b
Assumption 1: b /\  
"Assumption 1" (line 1, column 5):
unexpected end of input
expecting white space, "(", "[", "{", unary formula or proposition
Assumption 1: b
Assumption 2 (leave blank to finish): a
Assumption 3 (leave blank to finish):
1 |   b   | Assumption
2 |   a   | Assumption
3 | (b∧a) | Conjunction 1,2
4 | (a∧b) | Commutation 3
```
