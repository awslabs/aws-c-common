FROM quay.io/bitriseio/android:alpha

ENV ANDROID_NDK_HOME /opt/android-ndk
ENV ANDROID_NDK_VERSION r12b
ENV CMAKE_VERSION 3.14.0


# ------------------------------------------------------
# --- Install required tools

RUN set -ex && \
    apt-get update -qq && \
    apt-get clean


# ------------------------------------------------------
# --- Android NDK

# download
RUN set -ex && \
    mkdir -p /tmp/android-ndk-tmp && \
    cd /tmp/android-ndk-tmp && \
    wget -q https://dl.google.com/android/repository/android-ndk-${ANDROID_NDK_VERSION}-linux-x86_64.zip && \
    # uncompress
    unzip -q android-ndk-${ANDROID_NDK_VERSION}-linux-x86_64.zip && \
    # move to its final location
    mv ./android-ndk-${ANDROID_NDK_VERSION} ${ANDROID_NDK_HOME} && \
    # remove temp dir
    cd ${ANDROID_NDK_HOME} && \
    rm -rf /tmp/android-ndk-tmp

# add to PATH
ENV PATH ${PATH}:${ANDROID_NDK_HOME}

###############################################################################
# CMake
###############################################################################
RUN set -ex && \
    mkdir -p /tmp/cmake-tmp && \
    cd /tmp/cmake-tmp && \
    curl -LO https://github.com/Kitware/CMake/releases/download/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}-Linux-x86_64.tar.gz && \
    tar xzf cmake-${CMAKE_VERSION}-Linux-x86_64.tar.gz --strip-components 1 -C /usr && \
    cmake --version
