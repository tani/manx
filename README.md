# Manx
CGによる意味解析器および文生成器

## Requirements

- SWI-Prolog

## Usage

```
$ swipl -l manx.pl # 読み込み

?- semparse([i, like,  cats]). -- 意味解析の実行
like(i, cats)

?- generate(3).
[i, like, cats] # like(i, cats) -- n単語の文の列挙
...
```

## Customization

`term(単語, 意味 # 範疇)` を加えることで語彙項目を増やせる。
