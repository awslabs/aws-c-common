FROM 123124136734.dkr.ecr.us-east-1.amazonaws.com/aws-common-runtime/ubuntu-16.04:x64

ENV NODE_VERSION="10.1.0"

###############################################################################
# NodeJS
###############################################################################
RUN set -ex \
    && curl "https://nodejs.org/download/release/v$NODE_VERSION/node-v$NODE_VERSION-linux-x64.tar.gz" -o node-v$NODE_VERSION-linux-x64.tar.gz \
    && tar -xzf "node-v$NODE_VERSION-linux-x64.tar.gz" -C /usr/local --strip-components=1 \
    && rm "node-v$NODE_VERSION-linux-x64.tar.gz" \
    && ln -s /usr/local/bin/node /usr/local/bin/nodejs \
    && node --version \
    && npm --version

###############################################################################
# Cleanup
###############################################################################
RUN set -ex \
    && cd \
    && apt-get update -qq \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*
