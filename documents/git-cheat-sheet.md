
# set up ssh-keys for use with `git`

  [this linked
  article](https://docs.github.com/en/authentication/connecting-to-github-with-ssh/adding-a-new-ssh-key-to-your-github-account)
  explains what needs to be done. Follow up if you have issues/need to
  ask questions!

# clone our repository 

  Once you have installed `git` on your computer, and once you have
  your `ssh key` set up for authentication to your github account (see
  previous step), you should be able to make a local copy of the
  repository by executing the following command in a `shell`:

  ```
  git clone git@github.com:gmcninch-tufts
  ```

  After executing that command, you will now have a directory
  `VERSEIM-2025` on your computer (below the current directory of the
  shell in which you executed the command).

# make your own `branch` in the repository

  To accomplish this on a `mac` or `linux` computer, type
  
  ```
  cd VERSEIM-2025
  git branch george
  ```
  
  (Here and below you should replace `"george"` with your name...!)
  That will create a new `branch` named `george`; confirm this as follows:
  
  ```
  git branch 
  
  =>
  george
  * main
  ```
  
  Now I should `checkout` the new branch, making it the branch I work on:
  
  ```
  git checkout george

  # or: git switch george
  
  ## confirm that this had some effect...
  git branch

  =>
  * george
  main
  ```
  
  (Note that the asterisk `*` should have moved...)
  
  When you make the branch, your new branch is identical to the `main`
  branch. But now you can modify the contents of your branch without
  affecting the contents of the `main` branch.
  
# let's see how to add content to your branch now

  Later on we'll see how to do a good bit of this directly in the `VS
  Code` editor, but maybe we'll understand it better if we do it first
  from the command line.
  
  Our `lean` work will be contained in the subdirectory `VERSEIM2025` of the repository.
  
  Let's enter that subdirectory and make a new directory to work inside.
  
  

  First make sure that while interacting with the shell, you are
  currently in the top directory `VERSEIM-2025`. (In `linux` or on a
  `mac` type `pwd` at the terminal prompt to see the current
  directory. In `windows` instead type `cwd`).
  
  For example, for me `pwd` reports
  ```
  pwd
  =>
  /home/george/Prof-VC/VERSEIM-2025
  ```
  
  Now proceed as follows
  ```
  # enter the work subdirectory
  cd VERSEIM2025
  
  # then make a subdirectory of that directory
  mkdir george
  
  # let's check by listing the contents of the current directory
  ls                           # or dir in windows
  =>
  Basic.lean  george  graph.lean  mcninch-math190
  
  # we see the new directory `george`
  ```
  
  Now let's make a dummy file in our new directory
  
  
  ```
  cd george
  touch empty.lean    # `linux` or `mac`
  # copy emtpy.lean+   # I'm told this is how you make an empty file in windows
  ```
  
  Now let's add these new contents to our the remote branch.
  The required sequence of steps is "add (or stage) - commit - push".
  
  
  
  ```
  # make sure we are on the right branch
  git branch
  =>
  * george
    main
  
  # now stage the new stuff 
  git add .   # the dot "." means "stage everything that has been changed"
  
  git commit -m "add new directory for lean work"
  
  ```
