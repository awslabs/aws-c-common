# escape=`

FROM mcr.microsoft.com/dotnet/framework/sdk:4.8-windowsservercore-ltsc2019

# Restore the default Windows shell for correct batch processing.
SHELL ["cmd", "/S", "/C"]

# copy dotnet core install file
# A copy of this can be found in s3://aws-crt-build-resources
COPY ["docker-assets/dotnet-install.ps1", "C:/Program Files/"]

# Install required dotnet distributions
RUN ["powershell.exe", "-File", "C:/Program Files/dotnet-install.ps1", "-Version", "5.0.100", "-InstallDir", "C:/Program Files/dotnet", "-NoCdn"]

ENV `
    # Enable detection of running in a container
    DOTNET_RUNNING_IN_CONTAINER=true `
    # Enable correct mode for dotnet watch (only mode supported in a container)
    DOTNET_USE_POLLING_FILE_WATCHER=true `
    # Skip extraction of XML docs - generally not useful within an image/container - helps performance
    NUGET_XMLDOC_MODE=skip

# Install PowerShell Core
RUN dotnet tool install --global PowerShell

# We want to use pwsh from now on
SHELL ["pwsh", "-Command"]

# Install Needed AWS PowerShell modules
RUN `
    Install-Module -Name AWS.Tools.Common -Scope CurrentUser -Force; `
    Install-Module -Name AWS.Tools.SecretsManager -Scope CurrentUser -Force; `
    Install-Module -Name AWS.Tools.SecurityToken -Scope CurrentUser -Force; `
    Install-Module -Name AWS.Tools.CodeArtifact -Scope CurrentUser -Force; `
    Install-Module -Name AWS.Tools.S3 -Scope CurrentUser -Force; `
    Install-Module -Name AWS.Tools.DynamoDBv2 -Scope CurrentUser -Force;

# The default shell for this image is pwsh
CMD ["pwsh"]

# Microsoft made building 3.5 with dotnet build difficult. We need to provide all the reference assemblies ourselves.
# A copy of the zipped assemblies can be found in: s3://aws-crt-build-resources
COPY ["docker-assets/35-reference-assemblies", "C:/Program Files (x86)/Reference Assemblies/Microsoft/Framework/.NETFramework/v3.5/Profile/Client"]

SHELL ["powershell"]

RUN iex ((New-Object System.Net.WebClient).DownloadString('https://chocolatey.org/install.ps1'))
RUN choco install cmake --installargs 'ADD_CMAKE_TO_PATH=System' -y --no-progress

# install visualcpp-build-tools
RUN powershell -NoProfile -InputFormat None -Command `
    choco install git 7zip -y; `
    choco install visualstudio2019-workload-vctools -y

#Install AWS CLI
RUN Invoke-WebRequest -UseBasicParsing https://s3.amazonaws.com/aws-cli/AWSCLI64PY3.msi -OutFile AWSCLI64PY3.msi; `
    Start-Process "msiexec.exe"  -ArgumentList '/i', 'AWSCLI64PY3.msi', '/qn', '/norestart' -Wait -NoNewWindow; `
    Remove-Item -Force AWSCLI64PY3.msi; 

#ENTRYPOINT C:\BuildTools\Common7\Tools\VsDevCmd.bat &&


