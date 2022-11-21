package com.gamehub.Model.Posts;

import com.gamehub.Model.Users.Gamer;

import java.time.LocalDateTime;
import java.util.List;

public class PostLike extends PostMultimedia {
    private String reacao;

    public PostLike(int id, Integer likes, LocalDateTime datetime, String jogo, String descricao, List<Tag> tags, String multimedia, Gamer gamer, String reacao) {
        super(id, jogo, descricao, likes, datetime, multimedia, gamer, tags);
        this.reacao = reacao;
    }

    public String getReacao() {
        return reacao;
    }

    public void setReacao(String reacao) {
        this.reacao = reacao;
    }

    @Override
    public String toString()
    {
        return super.toString() + "PostLike{" +
                "reacao='" + reacao + '\'' +
                '}';
    }
}
