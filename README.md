# Dione

Dione is a formal modeling framework to specify distributed protocols based on Input/Output automata.
In addition, we are also developing a (mostly) automated verification engine using Dafny program verifier.

## How to use Dione

### Prerequisite

Dione itself is a pure [Python] package and requires Python 3.7 or higher.
It uses [Dafny] as the verification engine and interacts with Dafny through shell pipelines.
We recommend users to use binary release of Dafny for Windows operating system.
Linux users can refer to [installation for Dafny] and install necessary dependencies for Dafny. 

Before running Dione, please change the path to the `DafnyServer.exe` in `setup.cfg`.
For example,
```ini
[dione]
dafny_server = C:\\path\to\DafnyServer.exe
```

[Python]: https://www.python.org/downloads/
[Dafny]: https://github.com/dafny-lang/dafny/releases
[installation for Dafny]: https://github.com/dafny-lang/dafny/wiki/INSTALL

### Running Dione

To run Dione in commandline, please run
```shell script
$ python -m dione path\to\ioa_file.py
```


## Modeling Language

See [Language Reference](docs/source/language.rst)


## Invariant Checking

TODO


## License

Dione is licensed under the University of Illinois/NCSA Open Source License.
See [LICENSE](LICENSE) for details.

