# The Mechanics of Proof

This repository contains the Lean code for the book [The Mechanics of Proof](https://hrmacbeth.github.io/math2001), by [Heather Macbeth](https://faculty.fordham.edu/hmacbeth1), developed for the course Math 2001 at Fordham University.

This is a fork of [`hrmacbeth/math2001`](https://github.com/hrmacbeth/math2001), updated to build on a current Lean toolchain. See [This fork](#this-fork) below.

The Lean files corresponding to each chapter of the book are in the folder [`Math2001`](Math2001).

## Setting up

Follow these four steps in order, especially step 4. Do not open the project in VS Code until the
first three have finished.

Windows is fine here, with or without WSL. Nothing below needs a Unix shell.

### 1. Install elan and VS Code

`elan` is Lean's version manager. It reads the [`lean-toolchain`](lean-toolchain) file in this
repository and fetches exactly the Lean version the project asks for, so it is the only piece of
Lean you install by hand.

Use the [manual installation instructions](https://lean-lang.org/install/manual/), which give
commands for Linux, macOS and Windows. Install `elan` and VS Code, then stop before opening any
project.

Installing `elan` also fetches the current stable Lean, as a default for work outside any
particular project. This project pins its own version in [`lean-toolchain`](lean-toolchain), so if
the two differ you will see Lean downloaded again during step 3. Nothing is wrong when that
happens. The two sit side by side without interfering.

Lean's [main quickstart guide](https://lean-lang.org/lean4/doc/quickstart.html) recommends the
opposite approach, installing the VS Code extension first and letting it set Lean up for you. That
works when you are starting from nothing, but it is the wrong route into an existing project like
this one. Use the manual instructions.

### 2. Clone the repository

```
git clone https://github.com/joewatt95/math2001.git
cd math2001
```

### 3. Fetch the dependencies and build

From inside the `math2001` directory:

```
lake exe cache get
lake build
```

The first command downloads a prebuilt Mathlib, which turns hours of compiling into a few minutes
of downloading. The second compiles everything else, both the tactics and theory in
[`Library`](Library) and the chapter files themselves. Both need to finish before the editor will
be much use.

`lake build` ends with a few hundred warnings saying `declaration uses 'sorry'`. Nothing has gone
wrong. Every exercise in the book is left as a `sorry` for you to replace, so those warnings are
the exercises waiting for you.

### 4. Only now, open the project in VS Code

From the same directory:

```
code .
```

VS Code will offer to install the recommended Lean 4 extension, which you should accept. Open any
file under [`Math2001`](Math2001) and the infoview should appear on the right.

If `code` is not on your PATH, open the `math2001` folder from VS Code's File menu instead.

This waits until last because the extension will install a Lean of its own if it opens a project
that looks unconfigured. That installation is separate from the one `elan` manages on the command
line, and the two then disagree about what has been built. Doing the command line work first means
the extension finds a finished project and simply uses it. Windows is where this bites most often.

## If the editor and the terminal disagree

This is the one thing most likely to go wrong, and it comes from doing step 4 before step 3.

Two symptoms give it away. `lake build` succeeds in a terminal while VS Code shows errors anyway,
often red squiggles on the `import` lines at the top of every file. Or VS Code offers to install
Lean even though you already installed `elan`. Either way the extension has set up a second Lean,
and the editor and the terminal are compiling against different copies.

To see which Lean each one is using, run this in a terminal from inside the project directory:

```
elan show
```

The active toolchain should be the one named in `lean-toolchain`, and `elan` will say it is
overridden by that file. Then compare against what the editor thinks, by running
`Lean 4: Show Setup Information` from the VS Code command palette.

To recover, quit VS Code completely. Check the terminal side is healthy by running `elan show` and
`lake build` in the project directory. Then reopen the project with `code .` from that same
directory. If VS Code offers to install Lean at that point, decline, because accepting is what
creates the second installation.

## This fork

This copy has been updated from Lean 4.3.0, which the book was written against, to Lean 4.33.1.
Mathlib follows the toolchain automatically.

Lean 4.33.1 was the latest stable release when this update was made, in September 2026. If `elan`
now gives you something newer by default, nothing here breaks. The version named in
[`lean-toolchain`](lean-toolchain) is the one this project builds with, whatever else you have
installed.

To check that the supporting code is healthy without the exercise warnings getting in the way,
`lake build Library` compiles just the tactics and theory, and should be completely silent.

The Gradescope autograder is not wired up here. [`PORTING.md`](PORTING.md) records what changed in
the update, which deprecated names were kept so the code still matches the book, and how to turn
the autograder back on.
