@echo off
rem Build the 3x-1 GPU verifier with the CUDA toolkit on PATH and the MSVC Build Tools that
rem built the atlas (the host compiler nvcc needs on Windows). Output goes to
rem .build\negative_floor_gpu\ at the repository root, which is not tracked.
setlocal
set VCVARS=C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Auxiliary\Build\vcvars64.bat
if not exist "%VCVARS%" (
    echo vcvars64.bat not found at "%VCVARS%"
    exit /b 2
)
call "%VCVARS%" >nul
cd /d "%~dp0"
set OUT=%~dp0..\..\..\..\.build\negative_floor_gpu
if not exist "%OUT%" mkdir "%OUT%"
nvcc -O3 -arch=sm_120 -allow-unsupported-compiler -Xcompiler /W3 -o "%OUT%\verify_3x1_gpu.exe" verify_3x1_gpu.cu
if errorlevel 1 (
    echo nvcc failed
    exit /b 1
)
echo built "%OUT%\verify_3x1_gpu.exe"
nvcc --version | findstr /C:"release"
