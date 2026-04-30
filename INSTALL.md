# Installing CertiRocq

## Get the code

Fetch the code:

```console
$ git clone git@github.com:CertiRocq/certirocq.git
```

Fetch the dependencies:

```console
$ git submodule update --init
```


## Install using opam (preferred)

First, pin the dependencies:

```console
$ opam pin -n -y submodules/metacoq
```

Next, pin CertiRocq:

```console
$ opam pin -n -y .
```

You can now install CertiRocq:

```console
$ opam install rocq-certirocq
```

Alternatively, if you only want to install the dependencies, you can run:

```console
$ opam install rocq-certirocq --deps-only
```

## Build & install manually

### Dependencies

If possible, install the dependencies using the opam instructions given above.

If that is not an option, you can instead use these "manual" instructions. Note that this approach will only work *if* your Rocq installation path is writable without root privileges.

Make sure that you do not have any of the dependencies installed already. From the `certirocq/` directory, run:

```console
$ make submodules
```


### Building the compiler

Once the dependencies are installed (either via opam or by the manual method), you can build the Rocq theories by running

```console
$ make all
```

The plugin, which depends on those theories, can be built by running

```console
$ make plugin
```

To install the theory & plugin, simply run

```console
$ make install
```


## Testing the installation

You can test the installation using the regression suites under `tests/`:

```console
$ make -C tests all
```

The Wasm tests under `tests/wasm/` additionally require `node` and
`wabt`. The CI configuration currently uses Node.js 22.
