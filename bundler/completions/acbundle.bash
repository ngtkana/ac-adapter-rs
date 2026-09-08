_acbundle() {
    local cur
    cur="${COMP_WORDS[COMP_CWORD]}"
    COMPREPLY=($(compgen -W "$(acbundle --list-crates 2>/dev/null) --keep-docs --keep-tests" -- "$cur"))
}

complete -F _acbundle acbundle
