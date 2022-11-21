package com.gamehub.Model.Posts;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.gamehub.Model.Users.Recompensa;

import javax.persistence.*;
import java.time.LocalDateTime;

@Entity
public class Tag {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private String tag;
    private String descricao;
    private LocalDateTime fim_torneio;

    @JsonIgnore
    @OneToOne(fetch = FetchType.EAGER)
    @JoinColumn(name = "recompensa_id")
    private Recompensa recompesa_ganha;


    public Tag(int id, String tag, String descricao) {
        this.id = id;
        this.tag = tag;
        this.descricao = descricao;
    }

    public Tag() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getTag() {
        return tag;
    }

    public void setTag(String tag) {
        this.tag = tag;
    }

    public String getDescricao() {
        return descricao;
    }

    public void setDescricao(String descricao) {
        this.descricao = descricao;
    }
}
