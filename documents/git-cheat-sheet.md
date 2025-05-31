
# set up ssh-keys for use with `git`

  [this article more-or-less explains what needs to be done](https://docs.github.com/en/authentication/connecting-to-github-with-ssh/adding-a-new-ssh-key-to-your-github-account)
  
  

# clone the repository 

  If you have installed `git` on your computer, and if you have your
  `ssh key` set up for authentication to your github account, you
  should be able to make a local copy of the repository by executing
  the following command in a `shell`:

  ```
  git clone git@github.com:gmcninch-tufts
  ```

  After executing that command, you will now have a directory
  `VERSEIM-2025` on your computer (below the current directory of the
  shell in which you executed the command).

# you should make your own branch in the repository

  on a `mac` or `linux` computer, I'd type 
  
  ```
  cd VERSEIM-2025
  git branch george
  ```
  
  That will create a new branch named george, as you can confirm
  
  ```
  git branch 
  
  =>
  george
  * main
  ```
  
  Now I should `checkout` the new branch, making it the branch I work on:
  
  ```
  git checkout george
  
  ## confirming...
  git branch

  =>
  * george
  main
  ```
  
  (Note that the asterisk `*` should have moved...)
  
# let's see how to add content to your branch now

  Let's make a new file. First make sure that you are in directory `VERSEIM-2025`
  
  
  (In `linux` or on a `mac` type `pwd` at the terminal prompt to see
  the current directory. In `windows` instead type `cwd`).
  
  We are going to work
  
  Now let's make a dummy file
  
  In `linux` or on a `mac`
  ```
  touch empty.txt
  ```
  
  In `windows`, I'm told that you should do
  ```
  copy empty.txt+
  ```
  
  to make an empty file. Let me know if that is mistaken!
  
  Now let's add this emtpy file to the 
