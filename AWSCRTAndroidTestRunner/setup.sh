#!/usr/bin/env bash

set -ex

if [ -z "$ANDROID_HOME" ]; then
    ANDROID_HOME=$HOME/android
fi

if [ -z "$ANDROID_API" ]; then
    export ANDROID_API=24
fi

if [ -z "$ANDROID_ABI" ]; then
    export ANDROID_ABI='default;x86'
fi

if [ -z "$ANDRDOID_NDK_VERSION" ]; then
    export ANDROID_NDK_VERSION=21.0.6113669
fi

CLI_TOOLS_URL=https://dl.google.com/android/repository/commandlinetools-linux-6200805_latest.zip

export PATH=$PATH:$ANDROID_HOME/tools:$ANDROID_HOME/tools/bin:$ANDROID_HOME/platform-tools
if ! [ -x "$(command -v sdkmanager)" ]; then
    # Install sdkmanager and update path
    curl -sSL -o /tmp/android-sdk-tools.zip $CLI_TOOLS_URL
    yes | sudo unzip -q /tmp/android-sdk-tools.zip -d $ANDROID_HOME
fi

mkdir -p ~/.android
touch ~/.android/repositories.cfg

# Accept all licenses
yes | sudo sdkmanager --licenses --sdk_root=$ANDROID_HOME
# Install required SDK/NDK/tools
sudo sdkmanager "emulator" "tools" "platform-tools" "ndk;${ANDROID_NDK_VERSION}" --sdk_root=$ANDROID_HOME
sudo sdkmanager "build-tools;25.0.2" "platforms;android-${ANDROID_API}" --sdk_root=$ANDROID_HOME
