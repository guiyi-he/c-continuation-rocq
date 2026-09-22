# derivative_dfa.txt 的 quiver 图

双击 `derivative_dfa.quiver.html`，然后点击“在 quiver 中打开完整 DFA”。
图中包含原文件全部 **182 个状态、364 条转移、136 个终态**。

- 蓝色 `init` 标记初态；绿色星号标记终态。
- 蓝色箭头标 `a`；橙色箭头标 `b`。
- 状态标签保留原始编号，水平方向按最短见证词长度分层。
- 自环、同一对状态之间的不同字符转移均分别保留。
- 本地页面提供见证词、bits、residues 和完整 continuation 查询。

总览默认缩小显示。可以在 quiver 中放大、平移并调整顶点与箭头的位置；
页面也提供“以较大比例打开”按钮。182 个状态的完整图连线较密集，建议放大局部阅读。

其他文件：

| 文件 | 用途 |
|---|---|
| `derivative_dfa.quiver.url.txt` | 完整 quiver 链接，可以复制到浏览器地址栏 |
| `derivative_dfa.quiver.json` | quiver 版本 0 的完整图数据；通过随附链接载入 |
| `derivative_dfa.quiver.metadata.json` | 原始状态详情、转移及源文件 SHA-256 |
| `derivative_dfa.quiver.preview.png` | 浏览器实际载入 quiver 后的总览截图 |

源文件更新后，在项目根目录重新生成：

```powershell
python tools/export_quiver.py derivative_dfa.txt --output-dir visualizations
```

转换器仅使用 Python 标准库。它核对状态、终态、完整转移表、可达性、
最短见证词重放以及 bits/residues 一致性，再验证编码链接的往返还原。
转换不会修改 `derivative_dfa.txt` 或 Rocq/OCaml 实现。
预览截图对应本次浏览器验证；转换器本身不重新拍摄截图。

格式依据：[quiver 官方链接编码实现](https://github.com/varkor/quiver/blob/master/src/quiver.mjs)，
使用 `[0, vertex_count, ...vertices, ...edges]` 的 UTF-8 JSON / Base64 URL 表示。
使用方式参见 [quiver 官方教程](https://github.com/varkor/quiver/blob/master/tutorial.md)。
