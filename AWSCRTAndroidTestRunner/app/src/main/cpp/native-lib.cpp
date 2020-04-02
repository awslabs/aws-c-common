#include <jni.h>
#include <string>
#include <sstream>

static bool s_tests_finished = false;
static size_t s_total_tests = 400;
static size_t s_test_idx = 0;

extern "C" JNIEXPORT void JNICALL
Java_software_amazon_awssdk_crt_awscrtandroidtestrunner_MainActivity_startTests(
        JNIEnv* env,
        jobject /* this */) {
}

extern "C" JNIEXPORT jstring JNICALL
Java_software_amazon_awssdk_crt_awscrtandroidtestrunner_MainActivity_currentTestName(
        JNIEnv *env,
        jobject /* this */) {
    std::stringstream test_name;
    test_name << "TEST " << s_test_idx++;
    if (s_test_idx >= s_total_tests) {
        s_tests_finished = true;
    }
    return env->NewStringUTF(test_name.str().c_str());
}

extern "C" JNIEXPORT jboolean JNICALL
Java_software_amazon_awssdk_crt_awscrtandroidtestrunner_MainActivity_testsFinished(
        JNIEnv *env,
        jobject /* this */) {
    return s_tests_finished;
}

extern "C" JNIEXPORT jint JNICALL
Java_software_amazon_awssdk_crt_awscrtandroidtestrunner_MainActivity_testsExitCode(
        JNIEnv *env,
        jobject /* this */) {
    return 0;
}

extern "C" JNIEXPORT jint JNICALL
Java_software_amazon_awssdk_crt_awscrtandroidtestrunner_NativeTestFixture_runTest(
        JNIEnv *env,
        jobject /* this */,
        jstring jni_name) {
    const char *test_name = env->GetStringUTFChars(jni_name, nullptr);
    printf("RUNNING %s\n", test_name);
    return 0;
}
