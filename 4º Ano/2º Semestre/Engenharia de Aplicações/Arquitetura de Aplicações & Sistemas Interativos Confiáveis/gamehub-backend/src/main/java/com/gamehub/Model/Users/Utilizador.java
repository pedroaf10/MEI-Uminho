package com.gamehub.Model.Users;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;

import javax.persistence.*;
import java.time.LocalDateTime;

@Entity
public class Utilizador {
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    private int id;
    private String email;
    private String password;

    @JsonIgnore
    @OneToOne(cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    @JoinColumn(name = "gamer_id")
    private Gamer gamer;

    public Utilizador(int id, String email, String password, Gamer gamer) {
        this.id = id;
        this.email = email;
        this.password = password;
        this.gamer = gamer;
    }

    public Utilizador(
            String email,
            String password) {
        this.email = email;
        this.password = password;
        this.gamer = new Gamer();
    }

    public Utilizador(
            @JsonProperty("email") String email,
            @JsonProperty("password") String password,
            @JsonProperty("nickname") String nickname,
            @JsonProperty("data_nascimento") LocalDateTime data_nascimento) {
        this.email = email;
        this.password = password;
        this.gamer = new Gamer(nickname, data_nascimento);
    }


    public Utilizador() {

    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getEmail() {
        return email;
    }

    public void setEmail(String email) {
        this.email = email;
    }

    public String getPassword() {
        return password;
    }

    public void setPassword(String password) {
        this.password = password;
    }

    public Gamer getGamer() {
        return gamer;
    }

    public void setGamer(Gamer gamer) {
        this.gamer = gamer;
    }

    @Override
    public String toString() {
        return "Utilizador{" +
                "id=" + id +
                ", email='" + email + '\'' +
                ", password='" + password + '\'' +
                ", gamer=" + gamer +
                '}';
    }
}
