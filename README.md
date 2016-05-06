# Stellite

A tool for converting C11-like code into [Alloy](http://alloy.mit.edu/alloy/)
predicates. Built using F# and FParsec. 

Portions of Stellite's code were adapted with permission from
[Starling](https://github.com/septract/starling-tool). 

Warning: Stellite is pre-alpha researchware. It may not do what you want, or
indeed anything at all. 

Stellite is a [type of alloy](https://en.wikipedia.org/wiki/Stellite). 

## Usage

Stellite takes optimisations written in a simple C-like language: see
`examples/pass/RRelim.stl` for an example. 

To check a single example, call 
 > `$ ./runtest.sh examples/pass/RRelim.stl`

To check all the examples, call
 > `$ ./test.sh` 

## People

* [Mike Dodds](https://www-users.cs.york.ac.uk/~miked/)


## License 

MIT; see `LICENSE.md`. 
