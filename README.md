# Stellite

A tool for converting C11-style program transformations into an
[Alloy](http://alloy.mit.edu/alloy/) model, and then checking the
transformation's validity. Built using F# and FParsec. 

Portions of Stellite's code were adapted with permission from
[Starling](https://github.com/septract/starling-tool). 

A draft paper on the theory underlying Stellite is available [here](https://www-users.cs.york.ac.uk/~miked/publications/verifying_prog_trans.pdf). 

## Usage

Stellite takes optimisations written in a simple C-like language: see
`examples/pass/RxlRxl-Rxl.stl` for an instance. 

To check a single example, call 
 > `$ ./runtest.sh <size> examples/pass/RxlRxl-Rxl.stl`

To check all the examples in `examples/pass` and `examples/fail`, call
 > `$ ./test.sh <size>` 

The parameter `<size>` is the maximum number of memory actions in the checked
histories. Size 8 is sufficient for most of our examples. 


## People

* [Mike Dodds](https://www-users.cs.york.ac.uk/~miked/)
* [Mark Batty](https://www.cs.kent.ac.uk/people/staff/mjb211/)
* [Alexey Gotsman](http://software.imdea.org/~gotsman/) 


## License 

MIT; see `LICENSE.md`. 
