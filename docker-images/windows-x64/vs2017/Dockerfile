# escape=`

FROM microsoft/windowsservercore

CMD [ "cmd.exe" ]

ADD https://download.microsoft.com/download/6/A/A/6AA4EDFF-645B-48C5-81CC-ED5963AEAD48/vc_redist.x64.exe /vc_redist.x64.exe
#ADD https://s3.amazonaws.com/elasticurl-pipeline/cd-builds/elasticurl/v0.2.15/win64/elasticurl.exe /bin/elasticurl.exe

# Add C:\bin (Elasticurl) to PATH
#RUN setx /M PATH "%PATH%;C:\bin" && set "PATH=%PATH%;c:\bin"; `
RUN mkdir c:\bin; `
    powershell Invoke-WebRequest https://s3.amazonaws.com/elasticurl-pipeline/cd-builds/elasticurl/v0.2.15/win64/elasticurl.exe -OutFile c:\bin\elasticurl.exe; `
    c:\bin\elasticurl --version
    # install vcredist and delete installer
RUN    start /wait C:\vc_redist.x64.exe /quiet /norestart; `
    del /q c:\vc_redist.x64.exe; `
    # Install chocolatey
    powershell -NoProfile -ExecutionPolicy unrestricted -Command "(iex ((new-object net.webclient).DownloadString('https://chocolatey.org/install.ps1')))" && SET "PATH=%PATH%;%ALLUSERSPROFILE%\chocolatey\bin"; `
    choco install -y git 7zip python3; `
    # install cmake
    choco install cmake --installargs 'ADD_CMAKE_TO_PATH=""System""' -y; `
    # install python
    choco install -y python3 --install-arguments "/InstallDir:C:\\python3 /PrependPath=1"; `
    # update path and test
    refreshenv; `
    cmake --version; `
    python --version

# Install Visual C++ Build Tools, as per: https://chocolatey.org/packages/visualcpp-build-tools
RUN powershell -NoProfile -InputFormat None -Command `
    choco install visualcpp-build-tools -version 15.0.26228.20170424 -y; `
    Write-Host 'Waiting for Visual C++ Build Tools to finish'; `
    Wait-Process -Name vs_installer; `
    setx /M PATH "%PATH%;C:\Program Files (x86)\Microsoft Visual Studio\2017\BuildTools\MSBuild\15.0\Bin"; `
    msbuild -version
