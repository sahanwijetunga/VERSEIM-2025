
# ongoing tasks
## updating your local copy of the repository

  You should do work in your personal directory; that should avoid
  conflicts.

  When you want/need to get an updated copy of the repository, do the following.

  ```
  # commit your personal changes
  git switch george   ## just to make sure we are on the right switch. replace "george" with your name
  git add .           ## stage all your work
  git commit -m "some explanatory note for the commit"   ## commit your changes
  git push            ## push the changes to the remote server -- i.e. to github
  
  # pull the changes from the server on the main switch
  
  git switch main
  git pull
  git switch george   ## again, replace george by your name...
  git merge main
  ```
  
## making a pull request

  When you have some work you'd like to add to the main branch of the
  repository, proceed as follows:
  
  - update your local copy of the main repository by following the instructions above
  
  - edit the relevant files in `VERSEIM-2025/VERSEIM2025` 
  
  - push the edits to your branch as follows
  
    ```
	git switch george  # to make sure...
	git add .
    git commit -m "changes for pull-request"
	git push
	```
	
  - now in a browser, navigate to the github repository, at
    `https://github.com/gmcninch-tufts/VERSEIM-2025/`
	
  - at the top of the page, there is a row-menu with options `Code, Issues, Pull Requests, Actions, ...`
  
    choose `Pull Requests`
	
  - Now, on the right-hand side there should be a green button "New
    Pull Request". Push this to start making a pull-request.
	
  - You should be on a page labeled "Compare changes".
  
    There are two chooser-widgets.
	
	`base` should be `main`
	`compare` should be `<your branch>` (`george` in my case)
	
  - now push the green "create pull request" button
  
  That will generate an email to me to merge your branch to main.

# initial set-up

## set up ssh-keys for use with `git`

  [this linked
  article](https://docs.github.com/en/authentication/connecting-to-github-with-ssh/adding-a-new-ssh-key-to-your-github-account)
  explains what needs to be done. Follow up if you have issues/need to
  ask questions!

## clone our repository 

  Once you have installed `git` on your computer, and once you have
  your `ssh key` set up for authentication to your github account (see
  previous step), you should be able to make a local copy of the
  repository by executing the following command in a `shell`:

  ```
  git clone git@github.com:gmcninch-tufts/VERSEIM-2025.git
  ```

  After executing that command, you will now have a directory
  `VERSEIM-2025` on your computer (below the current directory of the
  shell in which you executed the command).

## make your own `branch` in the repository

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
  # first return to the top level 
  cd ../..    # this means change to the parent directory of the parent directory of george. In this case, that is
              # the "top directory" of the repo, namely `VERSEIM-2025`
  git add .   # the dot "." means "stage everything that has been changed"
  
              # we could have skipped the `cd ../..` and did instead `git add ../..` from inside the directory `george`
  
  git commit -m "add new directory for lean work"
  
  => [george da25f7f] add new directory for lean work
     1 file changed, 19 insertions(+), 10 deletions(-) 
	 create mode 100644 VERSEIM2025/george/empty.lean
  ```

  Now we have `staged` and `committed` our changes, and we need to
  push them to the remote server (i.e. "to `github`").


  ```
  git push
  ```	  
