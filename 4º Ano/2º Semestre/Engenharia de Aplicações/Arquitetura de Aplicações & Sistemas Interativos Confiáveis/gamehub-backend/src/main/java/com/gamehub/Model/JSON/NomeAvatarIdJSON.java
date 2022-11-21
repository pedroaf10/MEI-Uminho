package com.gamehub.Model.JSON;

import com.gamehub.Model.Users.Avatar;

public class NomeAvatarIdJSON {

    private int id;
    private Avatar avatar;
    private String nome;

    public NomeAvatarIdJSON(int id, Avatar avatar, String nome) {
        this.id = id;
        this.avatar = avatar;
        this.nome = nome;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public Avatar getAvatar() {
        return avatar;
    }

    public void setAvatar(Avatar avatar) {
        this.avatar = avatar;
    }

    public String getNome() {
        return nome;
    }

    public void setNome(String nome) {
        this.nome = nome;
    }
}
