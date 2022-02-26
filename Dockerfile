from ubuntu:18.04
COPY . /rest_api_synthesis
RUN maturin develop --release --strip
