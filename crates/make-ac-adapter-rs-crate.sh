#!/bin/bash

set -euC

# クレートを集めるときに無視するファイルを記述したファイルへの
# スクリプトディレクトリからの相対パスです。
readonly ACIGNORE_FILE='acignore.txt'

function main() {
    # ディクトリを移動します。
    local orig_dir=$(dirname "$0")
    cd "$orig_dir"

    # acignore を読みます。
    local ignore=($(cat "$ACIGNORE_FILE"))
    echo Ignored files:
    echo
    for file in "${ignore[@]}"; do
        echo -e "\t$file"
    done
    echo

    # 処理すべきファイルを集めます。
    declare -a modules=()
    for file in $(ls); do
        if [[ $(xargs -n1 <<< "${ignore[@]}" | grep -x "$file") ]]; then
            echo Skipped "$file"
        else
            modules+=("$file")
        fi
    done
    echo

    # 古い ac-adapter-rs を消去し、
    # 新しい ac-adapter-rs を追加して、そこに移動します。
    rm -rf ac-adapter-rs
    cargo new --lib ac-adapter-rs
    cd ac-adapter-rs

    # 各モジュールを集めます。
    rm src/lib.rs
    for module in "${modules[@]}"; do
        echo Processing $module...
        echo Members are $(ls "../$module")

        # snake_case に変更します。
        local snake_module=$(sed 's/-/_/g' <<< "$module")
        echo Snaked to "$snake_module"

        # 依存の追加です。
        cargo add ../"$module"/*

        # 分野モジュールを作ります。
        echo "pub mod $snake_module;" >> src/lib.rs

        # もともとクレートだったものをモジュールにします。
        for crate in $(ls "../$module"); do
            # snake_case に変更します。
            local snake_crate=$(sed 's/-/_/g' <<< "$crate")
            echo Snaked to "$snake_crate"
            echo "pub use $snake_crate;" >> src/"$snake_module".rs
        done

        echo
    done

    # 整えたり作ったりなどです
    cargo do check, build, clippy, test, doc

    # もとのディレクトリに戻ります。
    cd "$orig_dir"
}

main
