package software.amazon.awssdk.crt.awscrtandroidtestrunner

import androidx.appcompat.app.AppCompatActivity
import android.os.Bundle
import kotlinx.android.synthetic.main.activity_main.*
import java.util.Timer
import java.util.TimerTask
import kotlin.system.exitProcess

class MainActivity : AppCompatActivity() {

    val timer = Timer()

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContentView(R.layout.activity_main)

        sample_text.text = "Starting Tests..."

        startTests()
        timer.schedule(object: TimerTask() {
            override fun run() {
                runOnUiThread{ updateStatus() }
            }
        }, 0, 100)
    }

    fun updateStatus() {
        sample_text.text = currentTestName()
        if (testsFinished()) {
            val exitCode = testsExitCode()
            exitProcess(exitCode)
        }
    }

    external fun startTests()
    external fun currentTestName(): String
    external fun testsFinished(): Boolean
    external fun testsExitCode(): Int

    companion object {
        // Used to load the 'native-lib' library on application startup.
        init {
            System.loadLibrary("native-lib")
        }
    }
}
