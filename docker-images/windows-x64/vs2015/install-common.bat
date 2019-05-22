echo ON
:: Add C:\bin (Elasticurl) to PATH
setx /M PATH "%PATH%;C:\bin" && set "PATH=%PATH%;c:\bin" || goto :error
elasticurl --version || goto :error
:: install vcredist and delete installer
start /wait C:/vc_redist.x64.exe /quiet /norestart || goto :error
del /q c:\vc_redist.x64.exe || goto :error
:: install chocolatey
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -NoProfile -InputFormat None -ExecutionPolicy Bypass -Command "iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1'))" && SET "PATH=%PATH%;%ALLUSERSPROFILE%\chocolatey\bin"
choco install -y git 7zip || goto :error
choco install -y python3 --install-arguments "/InstallDir:C:\\python3 /PrependPath=1" || goto :error
choco install -y cmake --installargs 'ADD_CMAKE_TO_PATH=""System""' || goto :error
:: Update PATH and check installed programs
call RefreshEnv.cmd
cmake --version || goto :error
python --version || goto :error

exit 0

:error
echo "An error occurred"
exit /b 1