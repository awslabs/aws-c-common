#!/usr/bin/env bash

set -ex

export ANDROID_HOME=$HOME/android

if [ -z "$ANDROID_API" ]; then
    ANDROID_API=24
fi

if [ -z "$ANDROID_ABI" ]; then
    ANDROID_ABI='default;armeabi-v7a'
fi

export PATH=$PATH:$ANDROID_HOME/tools:$ANDROID_HOME/tools/bin:$ANDROID_HOME/platform-tools

# Install emulator and system image required
sdkmanager "emulator" "system-images;android-${ANDROID_API};${ANDROID_ABI}" --sdk_root=$ANDROID_HOME

echo no | avdmanager create avd --force -n test -k "system-images;android-${ANDROID_API};${ANDROID_ABI}"
$ANDROID_HOME/emulator/emulator64-arm -avd test -no-boot-anim -no-audio -no-window -gpu off -verbose &

# Wait for emulator to boot
anim_done=$(adb -e shell getprop init.svc.bootanim | grep 'stopped')
while [ -z "$booted" || -z "$anim_done" ]; do
    sleep 1
    anim_done=$(adb -e shell getprop init.svc.bootanim | grep 'stopped')
done

# unlock emulator screen
adb shell input keyevent 82
adb shell input keyevent 4