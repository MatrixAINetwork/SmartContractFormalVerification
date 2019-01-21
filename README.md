# SmartContractFormalVerification
Smart Contract formal verification Python program

安装过程：

1、安装python包

20:16	Packages installed successfully: Installed packages: 'z3'

20:21	Packages installed successfully: Installed packages: 'z3-solver'

20:24	Packages installed successfully: Installed packages: 'tokenlib'

20:26	Packages installed successfully: Installed packages: 'nltk'

20:27	Packages installed successfully: Installed packages: 'ply'

20:32	Packages installed successfully: Installed packages: 'document'

20:33	Packages installed successfully: Installed packages: 'docx'

然后选择
pip install python-docx 
pip uninstall docx

因为docx有问题，不能直接用

pip install graphviz
然后可以运行为：

python merify.py -ce -s test/DAO.sol

生成执行文件为：
python 3.6 已经自己安装了pip，所以只需要执行 pip install pyinstaller就可以了

编译可执行文件

 brew install upx

然后运行
python -O -m PyInstaller --onefile merify.py

