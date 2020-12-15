## Requirements
* Java 8
* Scala (tested with 2.13.3)

## Supported Platforms
* Linux

## Test Status

![Test Status](https://github.com/TomCranitch/wptool/workflows/Tests/badge.svg)


## Building

WPTool should build by typing `make` in the top-level directory. This should produce a shell script `wptool.sh` for running it.

## Running

Run `wptool.sh`, supplying a list of files to analyse as command line
arguments.

`-d` can be used to print additional debug information 

```
./wptool.sh file1 file2 ..
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

### Loops
The tool supports while and do-while loops. In both cases, an invariant should be specified. 
```
while(TRUE)
_invariant: z % 2 == 0
{
  z = z + 1;
  fence;
  x = r_secret;
  x = 0;
  fence;
  z = z + 1;
}
```

```
do
_invariant: TRUE
{
  r1 = z;
} while ((r1 % 2) != 0)
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
 * Pointers
 * Arrays
 
### Weak memory model
The logic for the weak memory model is currently not implemented

