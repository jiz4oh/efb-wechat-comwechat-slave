[教程地址](https://blog.honus.top/2022/10/15/580.html)

```docker
docker pull honus/efb-wechat-comwechat-slave:latest
```

部分已经支持的命令：

```
/search - 按关键字匹配好友昵称搜索联系人

/addtogroup - 按wxid添加好友到群组

/getmemberlist - 查看群组用户wxid

/at - 后面跟wxid，多个用英文,隔开，最后可用空格隔开，带内容。

/sendcard - 后面格式'wxid nickname'

/changename - 修改群组名称

/getstaticinfo - 可获取friends, groups, contacts信息
```

原版基础上新增 1 个配置，允许多开 comwechat，需要配合 `https://github.com/jiz4oh/python-comwechatrobot-http` 使用

```
#多开请将端口号修改为其他值，避免冲突
#比如 18888 => 18889
comwechat_url: http://127.0.0.1:18888
```
