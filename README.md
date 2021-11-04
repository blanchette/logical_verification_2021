# Logical Verification 2021: Installation Instructions

We have installation instructions for Windows, Linux, and macOS. As a backup
plan, we provide a virtual machine on which Lean is already installed.

These directions are adapted from the
[leanprover-community](https://leanprover-community.github.io/get_started.html#regular-install)
web page.

<details><summary>Windows</summary>


## Windows

These instructions are also covered in a [YouTube video](https://www.youtube.com/watch?v=y3GsHIe4wZ4).
This does not include the "Install our Logical Verification Repository" step.


### Get Lean

* Install Git for Windows: https://gitforwindows.org/.
  Accept all default answers during the installation
  (or, if you would like to minimize the installation,
  you may deselect all components on the "Select components"
  question).

* Start the newly installed `Git Bash` by searching for it in the Windows
  search bar.

* In Git Bash, run the command `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`.

* Press `[Enter]` to proceed with the installation.

* Run `echo 'PATH="$HOME/.elan/bin:$PATH"' >> $HOME/.profile`.

* Close Git Bash.


### Get Python

* Download the latest version of python [here](https://www.python.org/downloads/).

* Run the downloaded file (`python-3.x.x.exe`)

* Check `Add Python 3.x to PATH`.

* Choose the default installation.

* Open Git Bash (type `git bash` in the Start Menu)

* Run `which python`
  * The expected output is something like `/c/Users/<user>/AppData/Local/Programs/Python/Pythonxx-xx/python`. In this case, proceed to the next step.
  * If it's something like `/c/Users/<user>/AppData/Local/Microsoft/WindowsApps/python`, then
    * Did you follow the instruction to select `Add Python 3.x to PATH` during the installation?
      * If not, re-run the python installer to uninstall python and try again.
    * Otherwise, you need to disable a Windows setting.
      * Type `manage app execution aliases` into the Windows search prompt (start menu) and open the corresponding System Settings page.
      * There should be two entries `App Installer python.exe` and `App Installer python3.exe`. Ensure that both of these are set to `Off`.
    * Close and reopen Git Bash and restart this step.
  * If it is any other directory, you might have an existing version of Python. Ask the TAs for help.
  * If you get `command not found`, you should add the Python directory to your path. Google how to do this, or ask the TAs.

* Run `cp "$(which python)" "$(which python)"3`. This ensures that we can use the command `python3` to call Python.

* Test whether everything is working by typing `python3 --version` and `pip3 --version`. If both commands give a short output and no error, everything is set up correctly.
  * If `pip3 --version` doesn't give any output, run the command `python3 -m pip install --upgrade pip`, which should fix it.


### Configure Git

* Run `git config --global core.autocrlf input` in Git Bash.


### Install Lean Tools

* in Git Bash, run

  ```bash
  pip3 install mathlibtools
  ```


### Install and Configure the Editor

* Install [VS Code](https://code.visualstudio.com/).

* Launch VS Code.

* Click on the extension icon ![(image of icon)](img/new-extensions-icon.png)
  (or ![(image of icon)](img/extensions-icon.png) in older versions) in the side bar on the left edge of
  the screen (or press <kbd>Shift</kbd><kbd>Ctrl</kbd><kbd>X</kbd>) and search for `leanprover`.

* Select the `lean` extension (unique name `jroesch.lean`). There is also a
  `lean4` extension, but that one does not work for our course.

* Click "install" (In old versions of VS Code, you might need to click "reload" afterwards)

* Setup the default profile:

  * If you're using `git bash`, press `ctrl-shift-p` to open the command palette, and type
    `Select Default Profile`, then select `git bash` from the menu.

* Restart VS Code.

* Verify Lean is working, for example by saving a file `test.lean` and entering `#eval 1+1`.
  A green line should appear underneath `#eval 1+1`, and hovering the mouse over it you should see `2`
  displayed.


### Install Our Logical Verification Repository

* Close VSCode.

* Open Git Bash.

* In Git Bash, use `cd` to go to the directory you want to place the project in
  (a new folder will be created for it at that location). For instance, you can
  use `cd ~/Documents` to go to your personal Documents folder.

* Run these commands in Git Bash:

  ```bash
  leanproject get blanchette/logical_verification_2021
  cd logical_verification_2021
  lean --make lean
  ```

  The last command should produce a long list of warnings and errors which you
  can ignore.

* Launch VSCode.

* In the `File` menu, click `Open Folder`, and choose the folder
  `logical_verification_2021` (not one of its subfolders). If you used
  `~/Documents` above, it will be located in your `Documents` folder.

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by clicking
  the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>Debian/Ubuntu and Derivates</summary>


## Debian/Ubuntu and Derivates

These instructions are also in a [YouTube video](https://www.youtube.com/watch?v=02ff4WrW0FU),
not including the Logical Verification repository details.


### Install Lean

* Open a terminal, enter the following command and hit enter. (This will take
  some time.)

  ```bash
  wget -q https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile
  ```

* You may have to log out and log in again to make sure that the `lean` command
  is on your `PATH`.


### Install our Logical Verification Repository

* Use `cd` to go to the directory you want to place the project in. (A new
  folder will be created for it at that location.)

  ```bash
  leanproject get blanchette/logical_verification_2021
  cd logical_verification_2021
  lean --make lean
  ```

  The last command should produce a long list of warnings and errors which you
  can ignore.

* Launch VScode, either through your application menu or by typing `code`.

* On the main screen, or in the `File` menu, click `Open Folder`, and choose
  the folder `logical_verification_2021` (not one of its subfolders).

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>Other Linux Distros</summary>


## Other Linux Distros

Follow [these
instructions](https://leanprover-community.github.io/install/linux.html) and
proceed by the instructions "Install our logical verification repository" for
Debian/Ubunutu above.

</details>

<details><summary>macOS (Intel Macs)</summary>


## macOS (Intel Macs)

These instructions are also in a [YouTube
video](https://www.youtube.com/watch?v=NOGWsCNm_FY&ab_channel=leanprovercommunity),
not including the Logical Verification repository details.


### Install Lean

* Open a terminal, enter the following command and hit enter. (This will take
  some time.)

  ```bash
  /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib-tools/master/scripts/install_macos.sh)" && source ~/.profile
  ```


### Install our Logical Verification Repository

* Open a terminal.

* Use `cd` to go to the directory you want to place the project in (a new folder
  will be created for it at that location), for example you can use
  `~/Documents`.

  ```bash
  leanproject get blanchette/logical_verification_2021
  cd logical_verification_2021
  lean --make lean
  ```

  The last command should produce a long list of warnings and errors which you
  can ignore.

* Open VScode again.

* In the `File` menu, click `Open`, and choose the folder
  `logical_verification_2021` (not one of its subfolders). If you used
  `~/Documents` above, it will be in the `Documents` folder.

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

</details>

<details><summary>macOS (M1 Macs / Apple Silicon)</summary>

## macOS (M1 Macs / Apple Silicon)

Lean is not yet supported on M1 Macs. Specifically, `elan` – which is otherwise recommended (and installed) as part of the above instructions – will not be able to fetch Lean binaries on these devices.

In the meantime, you can try to set up an Intel installation using Rosetta:

 * [Install an Intel version of homebrew](https://stackoverflow.com/questions/64882584/how-to-run-the-homebrew-installer-under-rosetta-2-on-m1-macbook).

 * Follow [the detailed Lean installation
   instructions](https://leanprover-community.github.io/install/macos_details.html),
   ensuring you use the Intel version of homebrew.

* Open a Rosetta terminal.

* Use `cd` to go to the directory you want to place the project in (a new folder
  will be created for it at that location), for example you can use
  `~/Documents`.

  ```bash
  leanproject get blanchette/logical_verification_2021
  cd logical_verification_2021
  lean --make lean
  ```

  The last command should produce a long list of warnings and errors which you
  can ignore.

* Open VScode again.

* In the `File` menu, click `Open`, and choose the folder
  `logical_verification_2021` (not one of its subfolders). If you used
  `~/Documents` above, it will be in the `Documents` folder.

* In the file explorer on the left-hand side, you will find all exercises and
  homework in the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

There is a [Zulip thread](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/M1.20macs.html)
with some interim further details and advice. If you have trouble, feel free to ask the TAs for help.

</details>

<details><summary>Virtual Machine (for Any Operating System)</summary>

## Virtual Machine

* Download and install [VirtualBox](https://www.virtualbox.org/).
  (Other virtualization software should also work.)

* Download the virtual machine, `logical_verification_2021.ova` (3.3G), from
  [Google Drive](https://drive.google.com/file/d/1wFt7b0REC_8qqnO3CdOExi6iG6HIXZLQ/view).

  SHA256:
  ```
  c0d002a3bdb4b37ec9e69f6accc2e80846e70253a3e3abe7731436b85b93a854  logical_verification_2021.ova
  ```

* Open VirtualBox.

* Import the downloaded file via `File > Import Appliance`. This requires around
  7GB of disk space.

* Start the virtual machine by selecting `logical_verification_2021` and
  clicking the `Start` button. The virtual machine is configured to use 4
  processor cores and up to 5GB of RAM. (You can edit the virtual machine to
  change these values.) It uses around 4GB of RAM if you open all the Lean files
  in VSCode.

* Open VSCode by clicking on the blue ribbon icon on the desktop. VSCode should
  automatically open the folder `~/logical_verification_2021`. In the file
  explorer on the left-hand side, you will find all exercises and homework in
  the `lean` folder, as we upload them.

* You can retrieve the newest exercises and homework that we upload by
  clicking the two arrows forming a circle in the bottom left corner.

* If you need the password for the virtual machine at some point, it is
  `love`.

</details>
