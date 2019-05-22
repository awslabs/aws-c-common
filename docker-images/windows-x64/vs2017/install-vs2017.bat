echo ON
:: Install Visual C++ Build Tools, as per: https://chocolatey.org/packages/visualcpp-build-tools
choco install -y visualcpp-build-tools -version 14.0.25420.1 || goto :error
:: Add msbuild to PATH
setx /M PATH "%PATH%;C:\Program Files (x86)\MSBuild\14.0\bin" || goto :error
:: Test msbuild can be accessed without path
msbuild -version || goto :error

exit 0

:error
echo "An error occurred"
exit /b 1
