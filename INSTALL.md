# Building Stellite

(Instructions valid on OSX as of 3-4-16) 

## OPTION #1 (IDE) 

- Install Xamarin studio, which will install packages and automate the build process for you:
https://www.xamarin.com/studio

## OPTION #2 (command line) 

- Download and install: 
  * mono from http://www.mono-project.com/download/
  * fsharp from https://github.com/fsharp/fsharp

- Download Nuget from https://www.nuget.org/nuget.exe

- In the stellite-tool directory, run the following to download packages
  > `$ mono [path to NuGet]/NuGet.exe restore packages.config -PackagesDirectory packages`

- In stellite-tool, build by running 
  > `$ xbuild`
 
- The Stellite binary will be `starling-tool/bin/Debug/starling.exe`

- run Stellite with: 
  > `$ mono bin/Debug/stellite-tool.exe sample_opt.stl`

