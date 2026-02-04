FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y \
    autoconf \
    bison \
    build-essential \
    ca-certificates \
    curl \
    flex \
    git \
    help2man \
    libfl-dev \
    perl \
    python3 \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/verilator/verilator.git /tmp/verilator \
    && cd /tmp/verilator \
    && git checkout ad85d8981 \
    && autoconf \
    && ./configure \
    && make -j$(nproc) \
    && make install \
    && rm -rf /tmp/verilator

ENV VERILATOR_ROOT=/usr/local/share/verilator
