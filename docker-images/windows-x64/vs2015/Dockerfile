# escape=`

FROM microsoft/windowsservercore

CMD [ "cmd.exe" ]

ADD https://download.microsoft.com/download/6/A/A/6AA4EDFF-645B-48C5-81CC-ED5963AEAD48/vc_redist.x64.exe /vc_redist.x64.exe
ADD https://s3.amazonaws.com/elasticurl-pipeline/cd-builds/elasticurl/v0.2.15/win64/elasticurl.exe /bin/elasticurl.exe
ADD install-common.bat /install-common.bat
ADD install-vs2015.bat /install-vs2015.bat

# Install common deps
RUN install-common.bat
# Install VS2015
RUN install-vs2015.bat
