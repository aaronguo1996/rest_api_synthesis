from ubuntu:18.04

RUN apt-get -y update && apt-get install --no-install-recommends -y \ 
  python3-pip python3-venv curl build-essential python3-setuptools
RUN pip3 install maturin wheel
RUN python3 -m venv /venv
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

COPY . /rest_api_synthesis
WORKDIR /rest_api_synthesis

RUN pip3 install -r requirements.txt

RUN . /venv/bin/activate && maturin develop --release --strip
RUN . /rest_api_synthesis/apiphany/bench.py
