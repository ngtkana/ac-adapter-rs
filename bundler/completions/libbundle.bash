_libbundle() {
    local cur
    cur="${COMP_WORDS[COMP_CWORD]}"
    COMPREPLY=($(compgen -W "$(libbundle --list-crates 2>/dev/null) --keep-docs --keep-tests" -- "$cur"))
}

complete -F _libbundle libbundle
