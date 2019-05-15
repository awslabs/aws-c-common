FROM ubuntu:16.04

SHELL ["/bin/bash", "-c"]

###############################################################################
# Update apt
###############################################################################
RUN apt-get update -qq

###############################################################################
# Install prereqs
###############################################################################
RUN DEBIAN_FRONTEND=noninteractive apt-get -y install \
    git \
    curl \
    sudo \
    # Python
    python3 \
    python3-dev \
    python3-pip \
    build-essential \
    awscli \
    cmake \
    # For PPAs
    software-properties-common \
    apt-transport-https \
    libssl-dev

###############################################################################
# Elasticurl
###############################################################################
RUN set -ex \
    && mkdir -p /tmp/build \
    && mkdir -p /tmp/install \
    && cd /tmp/build \
    && git clone https://github.com/awslabs/aws-c-common.git \
    && git clone https://github.com/awslabs/aws-c-io.git \
    && git clone https://github.com/awslabs/s2n.git \
    && git clone https://github.com/awslabs/aws-c-compression.git \
    && git clone https://github.com/awslabs/aws-c-http.git \
    && pushd aws-c-common \
    && mkdir build \
    && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tmp/install -DCMAKE_PREFIX_PATH=/tmp/install .. \
    && cmake --build . --target install \
    && popd \
    && pushd s2n \
    && mkdir build \
    && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tmp/install -DCMAKE_PREFIX_PATH=/tmp/install .. \
    && cmake --build . --target install \
    && popd \
    && pushd aws-c-io \
    && mkdir build \
    && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tmp/install -DCMAKE_PREFIX_PATH=/tmp/install .. \
    && cmake --build . --target install \
    && popd \
    && pushd aws-c-compression \
    && mkdir build \
    && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/tmp/install -DCMAKE_PREFIX_PATH=/tmp/install .. \
    && cmake --build . --target install \
    && popd \
    && pushd aws-c-http \
    && mkdir build \
    && cd build \
    && cmake -DCMAKE_INSTALL_PREFIX=/usr/local -DCMAKE_PREFIX_PATH=/tmp/install .. \
    && cmake --build . --target install \
    && popd \
    && $(elasticurl --help) || [ $? == 1 ]
RUN apt-get remove -y libssl-dev

###############################################################################
# OpenSSL
###############################################################################
RUN DEBIAN_FRONTEND=noninteractive apt-get -y install gcc g++
RUN set -ex \
    && ([ -d /opt/openssl ] && rm -rf /opt/openssl) || true \
    && mkdir -p /tmp/build \
    && cd /tmp/build \
    && git clone https://github.com/openssl/openssl.git \
    && pushd openssl \
    && git checkout OpenSSL_1_1_1-stable \
    && ./config -fPIC \
        no-md2 no-rc5 no-rfc3779 no-sctp no-ssl-trace no-zlib no-hw no-mdc2 \
        no-seed no-idea no-camellia no-bf no-dsa no-ssl3 no-capieng \
        no-unit-test no-tests \
        -DSSL_FORBID_ENULL -DOPENSSL_NO_DTLS1 -DOPENSSL_NO_HEARTBEATS \
        --prefix=/opt/openssl --openssldir=/opt/openssl \
    && make -j \
    && make install_sw \
    && LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/opt/openssl/lib /opt/openssl/bin/openssl version
RUN DEBIAN_FRONTEND=noninteractive apt-get remove -y gcc g++ \
    && apt autoremove -y

###############################################################################
# Cleanup
###############################################################################
RUN set -ex \
    && apt-get update -qq \
    && apt-get clean \
    && rm -rf /tmp/*
