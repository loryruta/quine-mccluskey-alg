# Quine McCluskey algorithm

This is a Rust implementation of the Quine McCluskey algorithm.

## Usage

### How to install

To install the algorithm you have to download it from github:
```
git clone https://github.com/rutay/quine-mccluskey-alg
cd quine-mccluskey-alg
```

### Modify the input function

The binary function is defined as sum of min-terms and dont-cares and can be modified within the `main()` function.

```rust
// Definition of the binary function:
let mut f = BinaryFunction::new(4); // The `cardinality` tells how many inputs do we have.

// Here define the inputs combination that will give f(input) = 1.
// Giving in f.add_term(5), will result in f(0101) = 1. Not defined inputs will result in f(not_def_input) = 0.
f.add_term(Term::new(5));
f.add_term(Term::new(6));
f.add_term(Term::new(7));
f.add_term(Term::new(8));

// Here define the inputs combination that will give f(input) = x (or dont_care).
// Giving in f.add_term(10), will result in f(1010) = x.
f.add_dont_care(Term::new(10));
f.add_dont_care(Term::new(11));

// This is the function that will execute the algorithm and takes care of printing the results.
qmc_simplify(&f);
```

### Execute

I suggest to open the project using any Rust IDE, compile and run through it.
However, if you have the Rust toolchain accessible from terminal, and you're in the project directory, you can run the following command:

`cargo.exe run --color=always --package quine-mcclusky-alg --bin quine-mcclusky-alg`

### The output

If everything gone well, given the above inputs, you should see the following output:
```
(...)
[QMC] Prime implicants: (10-0,011-,01-1,101-)
[QMC] Essential implicants: (01-1,011-,10-0)
```

## Credits

Thanks to https://www.mathematik.uni-marburg.de/~thormae/lectures/ti1/code/qmc/ for allowing me to test.
