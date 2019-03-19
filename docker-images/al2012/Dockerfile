# Stock image build from internal AL2012.3 image on the wiki
FROM 123124136734.dkr.ecr.us-east-1.amazonaws.com/amzn-linux:2012.3

# workaround to allow yum to work in a container, stolen shamelessly from
# https://github.com/moby/moby/issues/10180#issuecomment-296977038
RUN set -ex \
    && rpm --rebuilddb \
    && yum update -y \
    && yum install -y tar gcc git openssl-devel

RUN set -ex \
    && cd /tmp \
    && curl -LO https://github.com/Kitware/CMake/releases/download/v3.14.0/cmake-3.14.0-Linux-x86_64.tar.gz \
    && tar xzf cmake-3.14.0-Linux-x86_64.tar.gz -C /usr --strip-components 1 \
    && cmake --version
