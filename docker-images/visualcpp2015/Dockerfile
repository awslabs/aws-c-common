escape=`

FROM microsoft/windowsservercore

# Install chocolatey
RUN @powershell -NoProfile -ExecutionPolicy unrestricted -Command "(iex ((new-object net.webclient).DownloadString('https://chocolatey.org/install.ps1'))) >$null 2>&1"

RUN choco install git 7zip -y
RUN choco install cmake --installargs 'ADD_CMAKE_TO_PATH=""System""' -y

# Install Visual C++ Build Tools, as per: https://chocolatey.org/packages/visualcpp-build-tools
RUN choco install visualcpp-build-tools -version 14.0.25420.1 -y

# Add msbuild to PATH
RUN setx /M PATH "%PATH%;C:\Program Files (x86)\MSBuild\14.0\bin"

# Test msbuild can be accessed without path
RUN msbuild -version

CMD [ "cmd.exe" ]
