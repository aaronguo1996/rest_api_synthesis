# rest_api_synthesis

# Using Evaluation Docker Image

## Build and Run Container

1. Install docker.
2. Run `docker build . -t latest apiphany`
3. Run `docker run -it apiphany`

## Building

This project is structured as a combined Rust/Python project (Rust is used for RE).
To build all the necessary components:

1. Install [maturin](https://github.com/PyO3/maturin).
2. Create a virtualenv and install all the Python requirements into the venv.
3. From the root directory, run `maturin develop --release --strip`.
4. The bench script should now be runnable from within the `apiphany` directory.
