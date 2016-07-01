# Building Stellite

(Instructions valid on OSX as of 3-4-16) 

There are two options for building Stellite.  In either case the Stellite
binary will be `stellite-tool/bin/Debug/stellite.exe`. For instructions on 
running benchmarks, see `README.md`.

## BUILD OPTION #1 (IDE) 

- Install Xamarin studio, which will install packages and automate the build process for you:
https://www.xamarin.com/studio

## BUILD OPTION #2 (command line) 

- Download and install: 
  * mono from http://www.mono-project.com/download/
  * fsharp from https://github.com/fsharp/fsharp

- Download Nuget from https://www.nuget.org/nuget.exe

- In the stellite-tool directory, run the following to download packages
  > `$ mono [path to NuGet]/NuGet.exe restore packages.config -PackagesDirectory packages`

- In stellite-tool, build by running 
  > `$ xbuild`


# Running Stellite tests in headless mode on a server

- Enter a shell by calling `$ screen` 

- Detach with CTRL-a CTRL-d

- To restore, call `$ screen -r`
