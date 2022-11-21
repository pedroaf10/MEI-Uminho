package com.gamehub.Model.Posts;

import javax.persistence.*;
import java.time.LocalDateTime;

@MappedSuperclass
public class Post {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int Id;
    private String jogo;

    @Column(columnDefinition = "TEXT")
    private String descricao;

    private Integer likes;

    private LocalDateTime datetime;

    public Post(int id, String jogo, String descricao, Integer likes, LocalDateTime datetime) {
        Id = id;
        this.jogo = jogo;
        this.descricao = descricao;
        this.likes = likes;
        this.datetime = datetime;
    }

    public Post(String jogo, String descricao, Integer likes, LocalDateTime datetime) {
        this.jogo = jogo;
        this.descricao = descricao;
        this.likes = likes;
        this.datetime = datetime;
    }

    public Post() {

    }

    public int getId() {
        return Id;
    }

    public void setId(int id) {
        Id = id;
    }

    public String getJogo() {
        return jogo;
    }

    public void setJogo(String jogo) {
        this.jogo = jogo;
    }

    public String getDescricao() {
        return descricao;
    }

    public void setDescricao(String descricao) {
        this.descricao = descricao;
    }

    public Integer getLikes() {
        return likes;
    }

    public void setLikes(Integer likes) {
        this.likes = likes;
    }

    public LocalDateTime getDatetime() {
        return datetime;
    }

    public void setDatetime(LocalDateTime datetime) {
        this.datetime = datetime;
    }

    @Override
    public String toString() {
        return "Post{" +
                "Id=" + Id +
                ", jogo='" + jogo + '\'' +
                ", descricao='" + descricao + '\'' +
                ", likes=" + likes +
                ", datetime=" + datetime +
                '}';
    }
}


