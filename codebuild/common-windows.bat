
mkdir %TEMP%\build
cd  %TEMP%\build
cmake %* -DPERFORM_HEADER_CHECK=ON -DCMAKE_BUILD_TYPE="RelWithDebInfo" %CODEBUILD_SRC_DIR% || goto error
msbuild.exe aws-c-common.vcxproj /p:Configuration=RelWithDebInfo || goto error
msbuild.exe tests/aws-c-common-assert-tests.vcxproj /p:Configuration=RelWithDebInfo || goto error
msbuild.exe tests/aws-c-common-tests.vcxproj /p:Configuration=RelWithDebInfo || goto error
ctest -V || goto error

del /S /F .\\**
cmake %* -DPERFORM_HEADER_CHECK=ON -DCMAKE_BUILD_TYPE="RelWithDebInfo" -DBUILD_SHARED_LIBS=ON %CODEBUILD_SRC_DIR% || goto error
msbuild.exe aws-c-common.vcxproj /p:Configuration=RelWithDebInfo || goto error
msbuild.exe tests/aws-c-common-assert-tests.vcxproj /p:Configuration=RelWithDebInfo || goto error
msbuild.exe tests/aws-c-common-tests.vcxproj /p:Configuration=RelWithDebInfo || goto error
ctest -V || goto error

goto :EOF

:error
echo Failed with error #%errorlevel%.
exit /b %errorlevel%
