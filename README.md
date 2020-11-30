## Requirements
* Java 8
* Scala (tested with 2.13.3)

## Supported Platforms
* Linux

## Test Status

![Test Status](https://github.com/TomCranitch/wptool/workflows/Tests/badge.svg)


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
global var a:

global var b:
_L: z % 2 == 0

global var secret:
_L: FALSE

gloabl var c:
_L: TRUE

local var d:
```
Variables must be defined at the start of the file, before any statements. 

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
* `==` equal to
* `!=` not equal to
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

## TODOs
### Unsupported language features
Below is an inconclusive list of unsupported language features.
 * Do-while loops
 * Atomics (this would also make CAS simpler to implement)
 * Pointers
 * Arrays
 
### Weak memory model
The logic for the weak memory model is currently not implemented

### Basic blocks
Implementing the tool using basic blocks, as opposed to the current while language, will make the tool more flexible. This would allow, in theory, to easily build C support.

### Improved feedback
The tool currently provides no feedback when it fails. This should be modified to, at a minimum, provide feedback on things like the loop invariant.


