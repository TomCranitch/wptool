## Requirements
* Java 8
* Scala (tested with 2.13.3)

## Supported Platforms
* Linux


## Building

WPTool should build by typing `make` in the top-level directory.

```
make
```

This should produce a shell script `wptool.sh` for running it.

## Running

Run `wptool.sh`, supplying a list of files to analyse as command line
arguments.

`-v` can be used ato print the P, D, and Gamma values after each statement

`-d` can be used to print additional debug information 

```
./wptool.sh file1 file2 ..
./wptool.sh -v file1 file2 ..
./wptool.sh -d file1 file2 ..
```

## Input file format

### Variable definitions
```
_var z:

_var x:
_L: z % 2 == 0

_var r_secret:
_L: FALSE

_var r12:
_L: TRUE
```
Variables must be defined at the start of the file, before any statements. Variables can have the mode `NoW` (No Write), `NoRW` (No Read/Write) or `RW` (Read/Write). Variables with `r_`  at the start of their names or of the form `r#` (where `#` is a sequence of digits) are Local, and automatically have the mode `NoRW`. All other variables are Global. If the L predicate is not defined for a variable, it will be `TRUE` by default. 

### Gamma_0 definitions
```
_Gamma_0: x -> LOW, r_secret -> HIGH, q[*] -> LOW
```
Defining the Gamma_0 is optional, but can occur between the variable definitions and the program. By default, P_0 will be set to `TRUE` and Gamma_0 will be set to `HIGH` for all variables in its domain. Predicates in P_0 can be separated with `,`. Gamma_0 can be specified for all members of an array with the wildcard `q[*]` for the array `q`.

### Assignment
```
x := 1
y := x
z := x + 2 - y
```

### If Statements
```
if (x == 0) {
  x := 1;
} else {
  x := 2;
}
```

### Supported operations
* `=` assignment
* `==` equality
* `<=` less than or equal to
* `<` less than
* `>=` greater than or equal to
* `>` greater than
* `!` logical not
* `&&` logical and
* `||` logical or
* `+` addition
* `-` subtraction
* `*` multiplication
* `/` integer division
* `%` modulus
* `|` bitwise or
* `&` bitwise and
* `^` bitwise xor
* `~` bitwise not

## Unsupported
Below is an inconclusive list of broken or unsupported language features.
 * While and do-while loops
 * Rely-guarantee and WMM
 * Local variables
