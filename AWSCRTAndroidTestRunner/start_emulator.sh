#!/usr/bin/env bash

set -ex

if [ -z "$ANDROID_HOME" ]; then
    ANDROID_HOME=$HOME/android
fi

if [ -z "$ANDROID_API" ]; then
    ANDROID_API=24
fi

if [ -z "$ANDROID_ABI" ]; then
    ANDROID_ABI='default;x86'
fi

PATH=$PATH:$ANDROID_HOME/tools:$ANDROID_HOME/tools/bin:$ANDROID_HOME/platform-tools

# Install emulator and system image required
sdkmanager "emulator" "system-images;android-${ANDROID_API};${ANDROID_ABI}" --sdk_root=$ANDROID_HOME

echo no | avdmanager create avd --force -n test -k "system-images;android-${ANDROID_API};${ANDROID_ABI}"
$ANDROID_HOME/emulator/emulator -avd test -no-audio -no-window -gpu off &

# Wait for emulator to boot
adb -e wait-for-device
booted=$(adb -e shell getprop sys.boot_completed | grep '1')
anim_done=$(adb -e shell getprop init.svc.bootanim | grep 'stopped')
while [ -z "$booted" || -z "$anim_done" ]; do
    sleep 1
    booted=$(adb -e shell getprop sys.boot_completed | grep '1')
    anim_done=$(adb -e shell getprop init.svc.bootanim | grep 'stopped')
done
